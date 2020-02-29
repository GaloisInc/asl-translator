{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Language.ASL.Formulas.Normalize
    ( deserializeAndNormalize
    , normalizeSymFnEnv
    ) where

import           Control.Monad ( liftM, unless )
import qualified Control.Monad.ST as ST
import           Control.Lens hiding (Index, (:>), Empty)

import           Data.Maybe ( catMaybes )
import qualified Data.Text as T
import qualified Data.HashTable.Class as H
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map

import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Context ( type (::>), pattern (:>), EmptyCtx, pattern Empty, (<++>), type (<+>) )
import qualified Data.Parameterized.Context as Ctx

-- to identify instructions
import qualified Dismantle.ARM.T32 as T32
import qualified Dismantle.ARM.A32 as A32
import qualified Dismantle.ARM.ASL as DA ( Encoding(..) )

import qualified What4.Interface as WI
import qualified What4.Symbol as WI
import qualified What4.Expr.Builder as WB
import           What4.Utils.Util ( SomeSome(..) )

import qualified Language.ASL.Formulas.Serialize as FS
import           Language.ASL.Types ( LabeledValue(..), projectValue, projectLabel )

data BuilderData t = NoBuilderData

-- | Normalize and re-serialize a serialized formula library.
normalizeSymFnEnv :: FS.SExpr -> IO FS.SExpr
normalizeSymFnEnv sexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  symFnsSer <- reverse <$> deserializeAndNormalize sym sexpr
  putStrLn $ "Finished normalization. Assembling Serialized Formulas."
  return $ FS.assembleSymFnEnv symFnsSer

data NormalizeSymFnEnv sym =
  NormalizeSymFnEnv { envAllFns :: FS.NamedSymFnEnv sym
                    , envNormFns :: [FS.SExpr]
                    }

allInstructionNames :: Set T.Text
allInstructionNames =
  Set.fromList (map (T.pack . DA.encName) (Map.elems A32.aslEncodingMap ++ Map.elems T32.aslEncodingMap))

shouldNormalize :: T.Text -> Bool
shouldNormalize nm = not $ Set.member nm allInstructionNames

-- | As formulas are read in, augment the formula environment with normalized
-- variants of each function.
deserializeAndNormalize :: forall sym t st fs
                                 . sym ~ WB.ExprBuilder t st fs
                                => sym
                                -> FS.SExpr
                                -> IO [FS.SExpr]
deserializeAndNormalize sym sexpr = do
  (_, NormalizeSymFnEnv _ normFns) <- FS.deserializeSymFnEnv' sym (NormalizeSymFnEnv Map.empty []) augmentEnv mkFun sexpr
  return normFns
  where
    mkFun :: NormalizeSymFnEnv sym -> FS.FunctionMaker IO sym
    mkFun nenv = FS.envFunctionMaker sym (FS.uninterpFunctionMaker sym) (envAllFns nenv)

    getSymFnEntry :: SomeSome (EmbeddedSymFn t) -> Maybe (T.Text, SomeSome (WI.SymFn sym))
    getSymFnEntry (SomeSome eSymFn) = case eSymFnInlined eSymFn of
      False -> Just (eSymFnName eSymFn, eSymFnSome eSymFn)
      True -> Nothing
    
    augmentEnv :: T.Text
               -> SomeSome (WI.SymFn sym)
               -> NormalizeSymFnEnv sym
               -> IO (NormalizeSymFnEnv sym)
    augmentEnv nm (SomeSome symFn) (NormalizeSymFnEnv env normfns) | not $ shouldNormalize nm = do
      putStrLn $ "Not Normalizing: " ++ (T.unpack nm)
      let serfun = FS.mkSymFnEnvEntry nm (FS.serializeSymFn symFn)
      return $! NormalizeSymFnEnv (Map.insert nm (SomeSome symFn) env) (serfun : normfns)
    augmentEnv nm (SomeSome symFn) (NormalizeSymFnEnv env normfns) | shouldNormalize nm = do
      putStrLn $ "Normalizing: " ++ (T.unpack nm)
      putStrLn $ "Number of functions so far: " ++ show (length normfns)
      (symFn', normSymFns) <- normalizeSymFn sym nm symFn
      let
        newnormfns = catMaybes $ map getSymFnEntry normSymFns
        newnormfnsSer = map (\(nm, SomeSome fn) -> FS.mkSymFnEnvEntry nm (FS.serializeSymFn fn)) newnormfns
        env' = foldr (\(nm,fn) env' -> Map.insert nm fn env') env newnormfns
      return $! NormalizeSymFnEnv (Map.insert nm (SomeSome symFn') env') (newnormfnsSer ++ normfns)


-- | A wrapper for treating ASL functions and instructions uniformly
data ExprForm f tp where
  ExprFormRet :: Ctx.Assignment f (ctx ::> a)
              -> ExprForm f (WI.BaseStructType (EmptyCtx ::> WI.BaseStructType ctx ::> a))
  -- ^ Functions may have a return value, which is tupled with the set of modified globals
  ExprFormSimple :: Ctx.Assignment f ctx
                 -> ExprForm f (WI.BaseStructType ctx)
  -- ^ Instructions only return a set of modified globals

mapExprForm :: Functor m
            => ExprForm f tp
            -> (forall ctx. Ctx.Assignment f ctx -> m (Ctx.Assignment g ctx))
            -> m (ExprForm g tp)
mapExprForm efm f = case efm of
  ExprFormRet asn -> ExprFormRet <$> (f asn)
  ExprFormSimple asn -> ExprFormSimple <$> (f asn)

someExprFormAsn :: ExprForm f tp -> Some (Ctx.Assignment f)
someExprFormAsn efm = case efm of
  ExprFormRet asn -> Some asn
  ExprFormSimple asn -> Some asn


-- | Normalize a symfn by expanding it into a collection of symfns that each project out
-- a single global. The resulting functions are collapsed together into a function which
-- unconditionally expands to its body. Later functions which call this will then
-- only see the expanded set of globals, making their own normalization possible.
normalizeSymFn :: forall sym t st fs args ret
                . sym ~ WB.ExprBuilder t st fs
               => sym
               -> T.Text
               -> WB.ExprSymFn t args ret
               -> IO (WB.ExprSymFn t args ret, [SomeSome (EmbeddedSymFn t)])
normalizeSymFn sym name symFn = case WB.symFnInfo symFn of
  WB.DefinedFnInfo args rawexpr eval
    | Ctx.AssignExtend realargs globalStructVar <- Ctx.viewAssign args
    , WI.BaseStructRepr globalReadReprs <- WB.bvarType globalStructVar -> do
    -- we un-tuple the globals here so we can rewrite functions as only depending on subsets of them
    (expr, globalReadVars) <- unpackStructInExpr sym globalStructVar rawexpr
    freshArgs <- FC.traverseFC (refreshBoundVar sym) realargs
    freshGlobalReads <- FC.traverseFC (refreshBoundVar sym) globalReadVars

    let allArgs = realargs <++> globalReadVars
    let allFreshArgs = freshArgs <++> freshGlobalReads
    
    (efm :: ExprForm (WI.SymExpr sym) ret) <- case WI.exprType expr of
      WI.BaseStructRepr (Empty :> WI.BaseStructRepr reprs :> argRepr) -> do
        globalsStruct <- WI.structField sym expr (Ctx.i1of2)
        exprs <- Ctx.traverseWithIndex (\idx _ -> WI.structField sym globalsStruct idx) reprs
        retVal <- WI.structField sym expr (Ctx.i2of2)
        return $ ExprFormRet (exprs :> retVal)
      WI.BaseStructRepr reprs -> do
        exprs <- Ctx.traverseWithIndex (\idx _ -> WI.structField sym expr idx) reprs
        return $ ExprFormSimple exprs
      _ -> badSignature
    
    embeddedSymFns <- mapExprForm efm $ \exprs -> do
      Ctx.traverseWithIndex (mkNamedSymFn allArgs allFreshArgs (WB.symFnName symFn) name) exprs

    expr' <- case embeddedSymFns of
      ExprFormRet (globaleSyms :> reteSym) -> do
        globalStruct <- WI.mkStruct sym $ FC.fmapFC eSymFnExpr globaleSyms
        retVal <- return $ eSymFnExpr reteSym
        WI.mkStruct sym (Ctx.empty :> globalStruct :> retVal)
      ExprFormSimple globaleSyms ->
        WI.mkStruct sym $ FC.fmapFC eSymFnExpr globaleSyms
    -- matching up the signatures here, we need a new bound variable for the outer
    -- globals struct, that we re-project onto our final expression after normalization
    
    freshGlobalStruct <- WI.mkStruct sym (FC.fmapFC (WI.varExpr sym) freshGlobalReads)    
    outerGlobalStructVar <- WI.freshBoundVar sym (WB.bvarName globalStructVar) (WB.bvarType globalStructVar)
    ogsVarExpr <- return $ WI.varExpr sym outerGlobalStructVar   
    outerGlobalStructExprs <- Ctx.traverseWithIndex (\idx _ -> WI.structField sym ogsVarExpr idx) globalReadReprs   
    expr'' <- WB.evalBoundVars sym expr' freshGlobalReads outerGlobalStructExprs
    
    symFn' <- WI.definedFn sym (WB.symFnName symFn) (freshArgs :> outerGlobalStructVar) expr'' (\_ -> True)
    return $ (symFn', viewSome (FC.toListFC SomeSome) (someExprFormAsn embeddedSymFns))
  _ -> fail $ "normalizeSymFn: Unexpected function signature: " ++ show symFn
  where
    badSignature :: IO a
    badSignature = fail $ "normalizeSymFn: Unexpected function signature: " ++ show symFn

    mkNamedSymFn :: forall ctx tp args'
                  . Ctx.Assignment (WB.ExprBoundVar t) args'
                 -> Ctx.Assignment (WB.ExprBoundVar t) args'
                 -> WI.SolverSymbol
                 -> T.Text
                 -> Ctx.Index ctx tp
                 -> WB.Expr t tp
                 -> IO (EmbeddedSymFn t args' tp)
    mkNamedSymFn allbvs freshAllBvs symbol name idx expr = do
      let
        idxint = Ctx.indexVal idx
        symbol' = symbol `appendToSymbol` ("__" ++ show idxint)
        name' = name <> "__" <> T.pack (show idxint)
      mkSymFn sym allbvs freshAllBvs symbol' name' expr


unpackStructInExpr :: forall sym t st fs globals tp
                    . sym ~ WB.ExprBuilder t st fs
                   => sym
                   -> WB.ExprBoundVar t (WI.BaseStructType globals)
                   -> WB.Expr t tp
                   -> IO (WB.Expr t tp, Ctx.Assignment (WB.ExprBoundVar t) globals)
unpackStructInExpr sym globalsbv expr = do
  WI.BaseStructRepr globalsRepr <- return $ WB.bvarType globalsbv
  freshGlobalsBvs <- Ctx.traverseWithIndex mkStructBV globalsRepr
  freshStruct <- WI.mkStruct sym (FC.fmapFC (WI.varExpr sym) freshGlobalsBvs)
  expr' <- WB.evalBoundVars sym expr (Ctx.singleton globalsbv) (Ctx.singleton freshStruct)
  return (expr', freshGlobalsBvs)
  where
    mkStructBV :: forall tp'. Ctx.Index globals tp' -> WI.BaseTypeRepr tp' -> IO (WB.ExprBoundVar t tp')
    mkStructBV idx repr = WI.freshBoundVar sym ((WB.bvarName globalsbv) `appendToSymbol` ("_" ++ show (Ctx.indexVal idx))) repr

labeledVarExpr :: WB.ExprBuilder t st fs -> WB.ExprBoundVar t tp -> LabeledValue WI.SolverSymbol (WB.Expr t) tp
labeledVarExpr sym bv = LabeledValue (WB.bvarName bv) (WI.varExpr sym bv)

refreshBoundVar :: forall sym t tp st fs
                  . sym ~ WB.ExprBuilder t st fs
                 => sym
                 -> WB.ExprBoundVar t tp
                 -> IO (WB.ExprBoundVar t tp)
refreshBoundVar sym bv = WI.freshBoundVar sym (WB.bvarName bv) (WB.bvarType bv)

refreshBoundVars :: forall sym t fnargs st fs
                  . sym ~ WB.ExprBuilder t st fs
                 => sym
                 -> Ctx.Assignment (LabeledValue WI.SolverSymbol (WB.Expr t)) fnargs
                 -> IO (Ctx.Assignment (WB.ExprBoundVar t) fnargs)
refreshBoundVars sym bvs = FC.traverseFC refreshBV bvs
  where
    refreshBV :: forall tp. LabeledValue WI.SolverSymbol (WB.Expr t) tp -> IO (WB.ExprBoundVar t tp)
    refreshBV (LabeledValue nm expr) = WI.freshBoundVar sym nm (WI.exprType $ expr)

appendToSymbol ::  WI.SolverSymbol -> String -> WI.SolverSymbol
appendToSymbol symbol str =
  let
    symbolstr = T.unpack $ WI.solverSymbolAsText symbol
  in WI.safeSymbol (symbolstr ++ str)

-- | An 'EmbeddedSymFn' wraps a 'WB.ExprSymFn' which only takes a subset of all
-- the available bound variables.
data EmbeddedSymFn t allargs tp where
  EmbeddedSymFn :: { eSymFnName :: T.Text
                   , eSymFnEmbedding :: Ctx.CtxEmbedding fnargs allargs
                   -- ^ proof that the function arguments are a subset of all available bound variables
                   , _eSymFnFn :: WB.ExprSymFn t fnargs tp
                   -- ^ the function with a narrowed scope of arguments
                   -- (unusable accessor due to existential types)
                   , eSymFnExpr :: WB.Expr t tp
                   -- ^ the function applied to fresh variants of the subset of available bound variables.
                   -- i.e. it is equivalent to the source expression, but it now contains the corresponding
                   -- bound variables for the in-construction normalized function.
                   , eSymFnInlined :: Bool
                   -- ^ true if this function is always inlined (and therefore does not need to be serialized)
                   } -> EmbeddedSymFn t allargs tp

eSymFnSome :: EmbeddedSymFn t allargs tp -> SomeSome (WB.ExprSymFn t)
eSymFnSome (EmbeddedSymFn _ _ symFn _ _) = SomeSome symFn

applyEmbeddingAsn :: Ctx.Size ctx
                  -> Ctx.CtxEmbedding ctx ctx'
                  -> Ctx.Assignment f ctx'
                  -> Ctx.Assignment f ctx
applyEmbeddingAsn sz ctxe asn = Ctx.generate sz (\idx -> asn Ctx.! Ctx.applyEmbedding' ctxe idx)

-- | Represent an expression as a function of a subset of the given bound variables.
-- The expression is examined for which bound variables it actually depends on in order to
-- calculate its result, and is then abstracted into a function over only those variables.
mkSymFn :: forall sym t st fs allargs tp
         . sym ~ WB.ExprBuilder t st fs
        => sym
        -> Ctx.Assignment (WB.ExprBoundVar t) allargs
        -- ^ all in-scope bound variables that may appear in the given expression
        -> Ctx.Assignment (WB.ExprBoundVar t) allargs
        -- ^ fresh variants of the above bound variables, representing the arguments to the normalized function
        -> WI.SolverSymbol
        -> T.Text
        -> WB.Expr t tp
        -- ^ the expression representing the final result of a single struct member
        -> IO (EmbeddedSymFn t allargs tp)
mkSymFn sym allbvs freshAllBvs symbol name expr = do
  usedbvsSet <- liftM (Set.unions . map snd) $ ST.stToIO $ H.toList =<< WB.boundVars expr
  SubAssignment embedding subbvs <- case mkSubAssigment usedbvsSet allbvs of
    Just subbvs -> return subbvs
    Nothing -> fail "Invalid expression: used bound variables not a subset of arguments."
  symFn <- WI.definedFn sym symbol subbvs expr (shouldInline subbvs)
  let outerbvs = applyEmbeddingAsn (Ctx.size subbvs) embedding freshAllBvs
  expr <- WI.applySymFn sym symFn (FC.fmapFC (WI.varExpr sym) outerbvs)
  return $ EmbeddedSymFn name embedding symFn expr (alwaysInline subbvs)
  where
    alwaysInline :: forall args
                  . Ctx.Assignment (WB.ExprBoundVar t) args
                 -> Bool
    alwaysInline bvs = case Ctx.viewAssign bvs of
      Ctx.AssignExtend Ctx.Empty bv | Just Refl <- testEquality (WI.varExpr sym bv) expr -> True
      _ -> False
    
    shouldInline :: forall args
                  . Ctx.Assignment (WB.ExprBoundVar t) args
                 -> Ctx.Assignment (WB.Expr t) args
                 -> Bool
    shouldInline bvs args = alwaysInline bvs || FC.allFC WI.baseIsConcrete args

data SubAssignment f ctx where
  SubAssignment :: Ctx.CtxEmbedding ctx' ctx -> Ctx.Assignment f ctx' -> SubAssignment f ctx

mkSubAssigment :: OrdF f
               => Set (Some f)
               -> Ctx.Assignment f ctx
               -> Maybe (SubAssignment f ctx)
mkSubAssigment elems asn = case Ctx.viewAssign asn of
  Ctx.AssignEmpty ->
    case Set.null elems of
      True -> return $ SubAssignment (Ctx.identityEmbedding Ctx.zeroSize) Ctx.empty
      False -> fail "Did not use all provided elements"
  Ctx.AssignExtend asn' f ->
    case Set.member (Some f) elems of
      True -> do
        SubAssignment embed subasn' <- mkSubAssigment (Set.delete (Some f) elems) asn'
        return $ SubAssignment (Ctx.extendEmbeddingBoth embed) (subasn' :> f)
      False -> do
        SubAssignment embed subasn' <- mkSubAssigment elems asn'
        return $ SubAssignment (Ctx.extendEmbeddingRight embed) subasn'
