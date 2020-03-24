{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Language.ASL.Formulas.Normalize
    ( deserializeAndNormalize
    , normalizeSymFnEnv
    ) where

import           Prelude hiding ( fail )
import           GHC.Stack
import           Math.NumberTheory.Logarithms
import           GHC.TypeLits
import           Data.Kind

import           Control.Monad ( liftM, unless, forM, when, void )
import qualified Control.Monad.ST as ST
import           Control.Lens hiding (Index, (:>), Empty)
import           Control.Monad.Fail

import qualified Control.Monad.Trans.State as MS hiding ( get, put, gets, modify )
import qualified Control.Monad.Trans.Reader as MR hiding ( reader, local, ask, asks )
import qualified Control.Monad.Trans.Except as ME
import qualified Control.Monad.Reader as MR
import qualified Control.Monad.State as MS
import qualified Control.Monad.Except as ME
import qualified Control.Monad.IO.Class as IO
import qualified Control.Concurrent.MVar as IO
import qualified Control.Concurrent as IO

import           Data.Foldable
import           Data.Proxy
import qualified Data.Map.Ordered as OMap
import           Data.List ( intercalate )
import           Data.Maybe ( catMaybes, mapMaybe, fromJust )
import qualified Data.Text as T
import qualified Data.HashTable.Class as H
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IORef as IO
import qualified Text.PrettyPrint.ANSI.Leijen as LPP
import           Data.List.NonEmpty (NonEmpty(..))

import           Data.Parameterized.Pair
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import           Data.Parameterized.Map ( MapF )
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Context ( type (::>), pattern (:>), EmptyCtx, pattern Empty, (<++>), type (<+>) )
import qualified Data.Parameterized.Context as Ctx

-- from this package
import           Data.Parameterized.CtxFuns

import qualified What4.Interface as WI
import qualified What4.Symbol as WI
import qualified What4.SemiRing as WI
import qualified What4.Expr.Builder as WB
import qualified What4.Expr.WeightedSum as WSum
import           What4.Utils.Util ( SomeSome(..) )
import qualified What4.Expr.BoolMap as BM

import qualified What4.Serialize.Printer as WP

import qualified Language.ASL.Formulas.Serialize as FS
import           Language.ASL.Types ( LabeledValue(..), projectValue, projectLabel )

import           Debug.Trace

data BuilderData t = NoBuilderData

-- | Normalize and re-serialize a serialized formula library.
normalizeSymFnEnv :: FS.SExpr -> Maybe FS.SExpr -> IO (FS.SExpr, Maybe FS.SExpr)
normalizeSymFnEnv funsexpr minstexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  -- WB.startCaching sym
  NormalizeSymFnEnv env funsexprsrev proxyFns <- deserializeAndNormalize sym funsexpr
  let normFunSExprs = reverse $ (funsexprsrev)

  minstexpr' <- case minstexpr of
    Just instexpr -> do
      symFnEnv <- FS.getSymFnEnv instexpr
      instrPromises <- forM symFnEnv $ \(nm, instrSexpr) -> forkResult $ do
        reserializeInstr (Map.fromList proxyFns) nm instrSexpr
      (instrProxies, instrFuns) <- liftM unzip $ mapM (\f -> f >>= return) instrPromises
      return $ Just $ FS.assembleSymFnEnv $ map (uncurry FS.mkSymFnEnvEntry) (concat instrFuns ++ instrProxies)
    Nothing -> return Nothing
  funsexpr' <- return $ FS.assembleSymFnEnv $ map (uncurry FS.mkSymFnEnvEntry) normFunSExprs

  return $ (funsexpr', minstexpr')
  where
    serSymFn :: sym ~ WB.ExprBuilder t st fs
                => sym
                -> T.Text
                -> SomeSome (WI.SymFn sym)
                -> (T.Text, FS.SExpr)
    serSymFn _ nm (SomeSome symFn) =
      (nm, FS.serializeSymFn symFn)

forkResult :: IO a -> IO (IO a)
forkResult f = do
  mvar <- IO.newEmptyMVar
  tid <- IO.myThreadId
  void $ IO.forkFinally f $ \case
    Left ex -> do
      IO.throwTo tid ex
    Right result -> IO.putMVar mvar result
  return (IO.takeMVar mvar)

-- | Given the (serialized) function environment, normalize the given function and return
-- the resulting collection of functions. This includes a function with the original name that
-- calls all of the newly-generated helper functions.
reserializeInstr :: Map T.Text FS.SExpr
                 -> T.Text
                 -> FS.SExpr
                 -> IO ((T.Text, FS.SExpr), [(T.Text, FS.SExpr)])
reserializeInstr env name sexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  doSerialize sym
  where
    doSerialize :: forall sym t st fs
                 . sym ~ WB.ExprBuilder t st fs
                => WI.IsSymExprBuilder sym
                => sym
                -> IO ((T.Text, FS.SExpr), [(T.Text, FS.SExpr)])
    doSerialize sym = do
      ref <- IO.newIORef (Map.empty :: Map T.Text (SomeSome (WI.SymFn sym)))
      let functionMaker = FS.lazyFunctionMaker sym (env, ref) `FS.composeMakers` FS.uninterpFunctionMaker sym
      SomeSome symFn <- FS.deserializeSymFn' functionMaker sexpr
      putStrLn $ "Normalizing Instruction: " ++ (T.unpack name)
      (symFn', normSymFns) <- normalizeSymFn sym name symFn
      return $! ((name, FS.serializeSymFn symFn'), (mapMaybe serializeEmbedded normSymFns))

    serializeEmbedded :: Some(EmbeddedSymFn t) -> Maybe (T.Text, FS.SExpr)
    serializeEmbedded (Some eSymFn)
      | SomeSome symFn <- eSymFnSome eSymFn
      , not (eSymFnInlined eSymFn)
      = Just (eSymFnName eSymFn, FS.serializeSymFn symFn)
    serializeEmbedded _ = Nothing

data NormalizeSymFnEnv sym =
  NormalizeSymFnEnv { envAllFns :: FS.NamedSymFnEnv sym
                    , envNormFns :: [(T.Text, FS.SExpr)]
                    , envProxyFns :: [(T.Text, FS.SExpr)]
                    }

-- | As formulas are read in, augment the formula environment with normalized
-- variants of each function.
deserializeAndNormalize :: forall sym t st fs
                                 . sym ~ WB.ExprBuilder t st fs
                                => sym
                                -> FS.SExpr
                                -> IO (NormalizeSymFnEnv sym)
deserializeAndNormalize sym sexpr = do
  snd <$> FS.deserializeSymFnEnv' sym (NormalizeSymFnEnv Map.empty [] []) augmentEnv mkFun sexpr

  where
    mkFun :: NormalizeSymFnEnv sym -> FS.FunctionMaker sym
    mkFun nenv = FS.envFunctionMaker sym  (envAllFns nenv) `FS.composeMakers` (FS.uninterpFunctionMaker sym)

    getSymFnEntry :: Some (EmbeddedSymFn t) -> Maybe (T.Text, SomeSome (WI.SymFn sym))
    getSymFnEntry (Some eSymFn) = case eSymFnInlined eSymFn of
      False -> Just (eSymFnName eSymFn, eSymFnSome eSymFn)
      True -> Nothing
    
    augmentEnv :: T.Text
               -> SomeSome (WI.SymFn sym)
               -> NormalizeSymFnEnv sym
               -> IO (NormalizeSymFnEnv sym)
    augmentEnv nm (SomeSome symFn) (NormalizeSymFnEnv env normfns proxyfuns) = do
      putStrLn $ "Normalizing Function: " ++ (T.unpack nm)
      putStrLn $ "Number of functions so far: " ++ show (length normfns)
      (symFn', normSymFns) <- normalizeSymFn sym nm symFn
      let
        newnormfns = catMaybes $ map getSymFnEntry normSymFns
        newnormfnsSer = map (\(nm, SomeSome fn) -> (nm, FS.serializeSymFn fn)) newnormfns
        env' = foldr (\(nm,fn) env' -> Map.insert nm fn env') env newnormfns
      return $! NormalizeSymFnEnv
        { envAllFns = Map.insert nm (SomeSome symFn') env'
        , envNormFns = newnormfnsSer ++ normfns
        , envProxyFns = (nm, FS.serializeSymFn symFn') : proxyfuns
        }

-- | A tree of Assignments over base types, reflecting any nested structure in the struct types.
data AssignmentTree f tp where
  AssignmentTreeLeaf :: f tp -> AssignmentTree f tp
  AssignmentTreeNode :: Ctx.Assignment (AssignmentTree f) ctx -> AssignmentTree f (WI.BaseStructType ctx)

traverseAssignmentTree :: Monad m
                       => (forall tp'. f tp' -> m (g tp'))
                       -> AssignmentTree f tp
                       -> m (AssignmentTree g tp)
traverseAssignmentTree f tree = case tree of
  AssignmentTreeLeaf a -> AssignmentTreeLeaf <$> f a
  AssignmentTreeNode nodes -> AssignmentTreeNode <$> FC.traverseFC (\tree' -> traverseAssignmentTree f tree') nodes


-- | Assignment tree traversal, with a record of the current path at each point.
traverseTreeWithIndex :: forall f g tp m
                         . Monad m
                        => (forall tp'. [Integer] -> f tp' -> m (g tp'))
                        -> AssignmentTree f tp
                        -> m (AssignmentTree g tp)
traverseTreeWithIndex f tree = go [] tree
  where
    go :: forall tp'. [Integer] -> AssignmentTree f tp' -> m (AssignmentTree g tp')
    go path tree =  case tree of
      AssignmentTreeLeaf a -> AssignmentTreeLeaf <$> f (reverse path) a
      AssignmentTreeNode nodes -> do
        nodes' <- Ctx.traverseWithIndex (\idx tree' -> go ((fromIntegral $ Ctx.indexVal idx) : path) tree') nodes
        return $ AssignmentTreeNode nodes'


collapseAssignmentTree :: Monad m
                       => (forall tp'. f tp' -> m (g tp'))
                       -> (forall ctx. Ctx.Assignment g ctx -> m (g (WI.BaseStructType ctx)))
                       -> AssignmentTree f tp
                       -> m (g tp)
collapseAssignmentTree g f tree = case tree of
  AssignmentTreeLeaf a -> g a
  AssignmentTreeNode nodes -> do
    nodes' <- FC.traverseFC (collapseAssignmentTree g f) nodes
    f nodes'

forIndex :: Applicative m
         => Ctx.Assignment f ctx
         -> (forall tp. Ctx.Index ctx tp -> f tp -> m (g tp))
         -> m (Ctx.Assignment g ctx)
forIndex asn f = Ctx.traverseWithIndex f asn

generateTree :: Monad m
             => (forall tp'. f tp' -> WI.BaseTypeRepr tp')
             -> (forall ctx tp'. f (WI.BaseStructType ctx) -> Ctx.Index ctx tp' -> m (f tp'))
             -> f tp
             -> m (AssignmentTree f tp)
generateTree getrepr f e = case getrepr e of
  WI.BaseStructRepr reprs -> do
    liftM AssignmentTreeNode $ forIndex reprs $ \idx _ -> do
      a <- f e idx
      generateTree getrepr f a
  _ -> return $ AssignmentTreeLeaf e


flattenTree :: AssignmentTree f tp -> [Some f]
flattenTree tree = case tree of
  AssignmentTreeLeaf a -> [Some a]
  AssignmentTreeNode nodes -> concat $ FC.toListFC flattenTree nodes

flattenZipTreePair :: AssignmentTree f tp -> AssignmentTree g tp -> [Pair f g]
flattenZipTreePair tree1 tree2 = case (tree1, tree2) of
  (AssignmentTreeLeaf l1, AssignmentTreeLeaf l2) -> [Pair l1 l2]
  (AssignmentTreeNode trees1, AssignmentTreeNode trees2) ->
    concat $ FC.toListFC (\(Const c) -> c) $ Ctx.zipWith (\a1 a2 -> Const (flattenZipTreePair a1 a2)) trees1 trees2

pairsToAssignments :: forall f g. [Pair f g] -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
pairsToAssignments = go (Ctx.empty, Ctx.empty)
  where
    go :: (Ctx.Assignment f ctx, Ctx.Assignment g ctx)
       -> [Pair f g]
       -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
    go (prev1, prev2) [] = Pair prev1 prev2
    go (prev1, prev2) (Pair a1 a2 : next) = (go $! (prev1 `Ctx.extend` a1, prev2 `Ctx.extend` a2)) next

-- | Project a tree of bound variables reflecting the type of a given bound variable.
getBoundVarsTree :: forall sym t st fs tp
                  . sym ~ WB.ExprBuilder t st fs
                 => sym
                 -> WB.ExprBoundVar t tp
                 -> IO (PairF (WB.Expr t) (AssignmentTree (WB.ExprBoundVar t)) tp)
getBoundVarsTree sym bv = case WB.bvarType bv of
  WI.BaseStructRepr _ -> do
    freshBVTree <- generateTree WB.bvarType mkSubBVar bv
    freshStruct <- collapseAssignmentTree (\bv -> return $ WI.varExpr sym bv) (WI.mkStruct sym) freshBVTree
    return $ PairF freshStruct freshBVTree
  _ -> return $ PairF (WI.varExpr sym bv) (AssignmentTreeLeaf bv)
  where
    mkSubBVar :: forall ctx tp'
               . WB.ExprBoundVar t (WI.BaseStructType ctx)
              -> Ctx.Index ctx tp'
              -> IO (WB.ExprBoundVar t tp')
    mkSubBVar bv idx = do
      let
        WI.BaseStructRepr reprs = WB.bvarType bv
        repr = reprs Ctx.! idx
      WI.freshBoundVar sym ((WB.bvarName bv) `appendToSymbol` ("_" ++ show (Ctx.indexVal idx))) repr

unpackArguments :: forall sym t st fs ctx tp
                 . sym ~ WB.ExprBuilder t st fs
                => sym
                -> Ctx.Assignment (WB.ExprBoundVar t) ctx
                -> WB.Expr t tp
                -> IO (WB.Expr t tp, Ctx.Assignment (AssignmentTree (WB.ExprBoundVar t)) ctx)
unpackArguments sym bvs expr = do
  (structExprs, vartrees) <- unzipPairF <$> FC.traverseFC (getBoundVarsTree sym) bvs
  expr' <- WB.evalBoundVars sym expr bvs structExprs
  return (expr', vartrees)

-- | Normalize a symfn by expanding it into a collection of symfns that each project out
-- a single global. The resulting functions are collapsed together into a function which
-- unconditionally expands to its body. Later functions which call this will then
-- only see the expanded set of globals, making their own normalization possible.
normalizeSymFn :: forall sym t st fs args ret
                . sym ~ WB.ExprBuilder t st fs
               => sym
               -> T.Text
               -> WB.ExprSymFn t args ret
               -> IO (WB.ExprSymFn t args ret, [Some (EmbeddedSymFn t)])
normalizeSymFn sym name symFn = case WB.symFnInfo symFn of
  WB.DefinedFnInfo args initexpr eval -> do
    -- e.g. f ( S :: (Int, (Bool, Int)) ) :: ((Int, Bool), Int) := ((- S[2:2], NOT S[2:1]), S[1] + S[2:2])
    
    -- elimate all struct-type bound variables by flattening them into multiple variables.
    -- the variables are stored in an 'AssignmentTree' to preserve their structure
    -- e.g.
    -- S :: (Int, (Bool, String))
    -- ==> (S_1 :: Int, (S_2_1 :: Bool, S_2_2 :: Int)) \\ S := (S_1, S_2), S_2 := (S_2_1, S_2_2)
    
    -- f S := ((- S[2:2], NOT S[2:1]), S[1] + S[2:2])
    -- ==> ((- S_2_2, NOT S_2_1), S_1 + S_2_2)
    (expr, boundVarTrees) <- unpackArguments sym args initexpr

    -- create fresh top-level bound variables for the outer function arguments
    -- S' :: (Int, (Bool, String))
    outerArgVars <- FC.traverseFC (refreshBoundVar sym) args
    outerArgExprs <- return $ FC.fmapFC (WI.varExpr sym) outerArgVars

    -- create a tree of projections for each (sub)field of these structs
    -- (S'[1], (S'[2:1], S'[2:2]))
    outerArgExprTree <- FC.traverseFC (generateTree WI.exprType (WI.structField sym)) outerArgExprs

    -- flatten both lists so all variables are visible
    -- ( [ S_1, S_2_1, S_2_2 ], [ S'[1], S'[2:1], S'[2:2] ] )
    Pair allArgs allFreshExprs <- return $
      pairsToAssignments $
      flattenZipTreePair (AssignmentTreeNode boundVarTrees) (AssignmentTreeNode outerArgExprTree)

    -- project out a unique function for each variable in the result type
    -- f S := ((- S_2_2, NOT S_2_1), S_1 + S_2_2)
    -- ==>
    -- f_1_1 (S_2_2) := - S_2_2
    -- f_1_2 (S_2_1) := NOT S_2_1
    -- f_2 (S_1, S_2_2) := S_1 + S_2_2
    let defaultBitSize = NR.knownNat @64
    eSymFnsTree <- evalRebindM sym name (BVBound defaultBitSize) $ do
      (expr', inline) <- simplifyInts expr
      resultTree <- generateTree WI.exprType (liftIO2 $ WI.structField sym) expr'
      traverseTreeWithIndex (mkSymFnAt allArgs allFreshExprs inline) resultTree

    eSymFnExprs <- traverseAssignmentTree (\eSymFn -> return $ eSymFnExpr eSymFn) eSymFnsTree

    -- reconstruct an expression equivalent to the original with the computed functions
    -- ==> ((f_1_1 (S'[2:2]), f_1_2 S'[2:1]), f_2 (S'[1], S'[2:2]))
    expr' <- collapseAssignmentTree return (WI.mkStruct sym) eSymFnExprs
    
    symFn' <- WI.definedFn sym (WB.symFnName symFn) outerArgVars expr' (\_ -> True)
    eSymFnList <- return $ map (\(Some eSymFn) -> Some eSymFn) $ flattenTree eSymFnsTree
    return $! (symFn', eSymFnList)
    where
      simplifyInts :: WB.Expr t tp
                   -> RebindM t (WB.Expr t tp, Bool)
      simplifyInts expr = do
        nfCache <- MS.gets rbNormFieldCache
        expr' <- withSym $ \sym -> normFieldAccs sym nfCache expr
        case exprDepthBounded 7 expr' of
          True -> return (expr', True)
          False -> do
            let doExtract = do
                  expr'' <- extractInts expr'
                  return (expr'', False)
            ME.catchError doExtract $ \case
              UnboundedInteger _ -> return (expr', True)
              e -> ME.throwError e

      mkSymFnAt :: forall allargs tp
                 . Ctx.Assignment (WB.ExprBoundVar t) allargs
                -> Ctx.Assignment (WB.Expr t) allargs
                -> Bool
                -> [Integer]
                -> WB.Expr t tp
                -> RebindM t (EmbeddedSymFn t tp)
      mkSymFnAt allArgs allFreshExprs inline idxpath e =
        let
          pathstr = "_SUB_" ++ pathToString idxpath
          symbol = appendToSymbol (WB.symFnName symFn) pathstr
          name' = name <> T.pack pathstr
        in mkSymFn allArgs allFreshExprs symbol name' inline e

-- | True if the expression is not any deeper than the given depth
exprDepthBounded :: Integer
                 -> WB.Expr t tp
                 -> Bool
exprDepthBounded 0 _ = False
exprDepthBounded i expr = case expr of
  WB.AppExpr appExpr -> FC.allFC (exprDepthBounded (i-1)) $ WB.appExprApp appExpr
  WB.NonceAppExpr nae ->
    case WB.nonceExprApp nae of
      WB.FnApp symFn args -> FC.allFC (exprDepthBounded (i-1)) $ args
  _ -> True

pathToString :: [Integer] -> String
pathToString idxpath = intercalate "_" $ map show idxpath

labeledVarExpr :: WB.ExprBuilder t st fs -> WB.ExprBoundVar t tp -> LabeledValue WI.SolverSymbol (WB.Expr t) tp
labeledVarExpr sym bv = LabeledValue (WB.bvarName bv) (WI.varExpr sym bv)

refreshBoundVar :: forall sym t tp st fs
                  . sym ~ WB.ExprBuilder t st fs
                 => sym
                 -> WB.ExprBoundVar t tp
                 -> IO (WB.ExprBoundVar t tp)
refreshBoundVar sym bv = WI.freshBoundVar sym (WB.bvarName bv) (WB.bvarType bv)

appendToSymbol ::  WI.SolverSymbol -> String -> WI.SolverSymbol
appendToSymbol symbol str =
  let
    symbolstr = T.unpack $ WI.solverSymbolAsText symbol
  in WI.safeSymbol (symbolstr ++ str)

-- | An 'EmbeddedSymFn' wraps a 'WB.ExprSymFn' which only takes a subset of all
-- the available bound variables.
data EmbeddedSymFn t tp where
  EmbeddedSymFn :: { eSymFnName :: T.Text
                   -- , eSymFnEmbedding :: Ctx.CtxEmbedding fnargs allargs
                   -- ^ proof that the function arguments are a subset of all available bound variables
                   , _eSymFnFn :: WB.ExprSymFn t fnargs tp'
                   -- ^ the function with a narrowed scope of arguments
                   -- (unusable accessor due to existential types)
                   , eSymFnExpr :: WB.Expr t tp
                   -- ^ the function applied to fresh variants of the subset of available bound variables.
                   -- i.e. it is equivalent to the source expression, but it now contains the corresponding
                   -- bound variables for the in-construction normalized function.
                   , eSymFnInlined :: Bool
                   -- ^ true if this function is always inlined (and therefore does not need to be serialized)
                   } -> EmbeddedSymFn t tp

eSymFnSome :: EmbeddedSymFn t tp -> SomeSome (WB.ExprSymFn t)
eSymFnSome (EmbeddedSymFn _ symFn _ _) = SomeSome symFn

applyEmbeddingAsn :: Ctx.Size ctx
                  -> Ctx.CtxEmbedding ctx ctx'
                  -> Ctx.Assignment f ctx'
                  -> Ctx.Assignment f ctx
applyEmbeddingAsn sz ctxe asn = Ctx.generate sz (\idx -> asn Ctx.! Ctx.applyEmbedding' ctxe idx)

-- | Represent an expression as a function of a subset of the given bound variables.
-- The expression is examined for which bound variables it actually depends on in order to
-- calculate its result, and is then abstracted into a function over only those variables.
mkSymFn :: forall t allargs tp
         . Ctx.Assignment (WB.ExprBoundVar t) allargs
        -- ^ all in-scope bound variables that may appear in the given expression
        -> Ctx.Assignment (WB.Expr t) allargs
        -- ^ fresh variants of the above bound variables, representing the arguments to the normalized function
        -> WI.SolverSymbol
        -> T.Text
        -> Bool
        -- ^ true if the outer function we are normalizing is inlined
        -> WB.Expr t tp
        -- ^ the expression representing the final result of a single struct member
        -> RebindM t (EmbeddedSymFn t tp)
mkSymFn allbvs outerExprs symbol name inline inexpr = do
  nfCache <- MS.gets rbNormFieldCache
  expr <- withSym $ \sym -> normFieldAccs sym nfCache inexpr
  usedbvsSet <- IO.liftIO $ liftM (Set.unions . map snd) $ ST.stToIO $ H.toList =<< WB.boundVars expr
  SubAssignment embedding subbvs <- case mkSubAssigment usedbvsSet allbvs of
    Just subbvs -> return subbvs
    Nothing -> withSym $ \sym ->
      fail $ "Invalid expression: used bound variables not a subset of arguments:" ++ showExpr expr
         ++ "\n Used:" ++ (show (map (\(Some bv) -> showExpr (WI.varExpr sym bv)) (Set.toList usedbvsSet)))
         ++ "\n All:" ++ (show (FC.toListFC (\bv -> showExpr (WI.varExpr sym bv)) allbvs))
  trivial <- alwaysInline expr subbvs
  let outerExprsSub = applyEmbeddingAsn (Ctx.size subbvs) embedding outerExprs
  case trivial of
    True -> withSym $ \sym -> do
      symFn <- WI.definedFn sym symbol subbvs expr (shouldInline trivial)
      expr2 <- WI.applySymFn sym symFn outerExprsSub
      return $ EmbeddedSymFn name symFn expr2 trivial
    False -> do
      case WI.exprType expr of
        WI.BaseIntegerRepr -> do
          Some (BVExpr expr2) <- extractBitV expr
          (expr3, Pair exprBVs exprArgs) <- extractIntBVs subbvs outerExprsSub expr2
          withSym $ \sym -> do
            symFn <- WI.definedFn sym symbol exprBVs expr3 (shouldInline trivial)
            expr4 <- WI.applySymFn sym symFn exprArgs
            expr5 <- WI.sbvToInteger sym expr4
            return $ EmbeddedSymFn name symFn expr5 trivial
        _ -> do
          (expr2, Pair exprBVs exprArgs) <- extractIntBVs subbvs outerExprsSub expr
          withSym $ \sym -> do
            symFn <- WI.definedFn sym symbol exprBVs expr2 (shouldInline trivial)
            expr3 <- WI.applySymFn sym symFn exprArgs
            return $ EmbeddedSymFn name symFn expr3 trivial
  where
    alwaysInline :: forall args
                  . WB.Expr t tp
                 -> Ctx.Assignment (WB.ExprBoundVar t) args
                 -> RebindM t Bool
    alwaysInline expr bvs = withSym $ \sym -> case Ctx.viewAssign bvs of
      Ctx.AssignEmpty -> return $ True
      Ctx.AssignExtend Ctx.Empty bv
       | Just Refl <- testEquality (WI.varExpr sym bv) expr
       , (WI.varExpr sym bv) == expr
       -> return $ True
      _ -> return $ inline || exprDepthBounded 2 expr

    shouldInline :: forall args
                  . Bool
                 -> Ctx.Assignment (WB.Expr t) args
                 -> Bool
    shouldInline isTrivial args = isTrivial || FC.allFC WI.baseIsConcrete args

showExpr :: WB.Expr t ret -> String
--showExpr e = (LPP.displayS (LPP.renderPretty 0.4 80 (WI.printSymExpr e)) "")
showExpr e = prettyResult $ WP.serializeExprWithConfig (WP.defaultConfig { WP.cfgAllowFreeVars = True, WP.cfgAllowFreeSymFns = True}) e

prettyResult :: WP.Result t  -> String
prettyResult res =
  let
    revVarEnv = Map.fromList $ map (\(Some bv, nm) -> (nm, (WI.solverSymbolAsText $ WB.bvarName bv) <> "(" <> T.pack (show (WB.bvarType bv)) <> ")")) (OMap.toAscList (WP.resFreeVarEnv res))
    revFnEnv = Map.fromList $ map (\(WP.SomeSymFn symFn, nm) -> (nm, WI.solverSymbolAsText $ WB.symFnName symFn)) (OMap.toAscList (WP.resSymFnEnv res))

    go a = case a of
      WP.AId nm -> case Map.lookup nm revVarEnv  of
        Just nm' -> WP.AId nm'
        _ -> case Map.lookup nm revFnEnv of
          Just nm' -> WP.AId nm'
          _ -> a
      _ -> a

  in T.unpack $ FS.printSExpr $ fmap go (WP.resSExpr res)

checkFieldsNorm :: forall t tp. String -> WB.Expr t tp -> IO (WB.Expr t tp)
checkFieldsNorm msg e = case e of
  WB.AppExpr appExpr -> do
    WB.traverseApp (checkFieldsNorm msg) (WB.appExprApp appExpr)
    go (WB.appExprApp appExpr)
  WB.NonceAppExpr nae ->
    case WB.nonceExprApp nae of
      WB.FnApp _ args -> do
        _ <- FC.traverseFC (checkFieldsNorm msg) args
        return e
  _ -> return e
  where
    go :: WB.App (WB.Expr t) tp -> IO (WB.Expr t tp)
    go (WB.StructField e' idx _) = do
      fail $ "checkFieldsNorm: unexpected structfield in expression: " ++ msg
    go _ = return e


-- | Normalize struct field accesses to reduce across if-then-else expressions.
-- i.e. (field 1 (ite b (W X) (Y Z))) --> (ite b W Y)
normFieldAccs :: forall sym st fs t tp
               . sym ~ WB.ExprBuilder t st fs
              => sym
              -> WB.IdxCache t (WB.Expr t)
              -> WB.Expr t tp
              -> IO (WB.Expr t tp)
normFieldAccs sym cache e = do
  case WB.exprMaybeId e of
    Just idx -> WB.lookupIdx cache idx >>= \case
      Just e' -> return e'
      Nothing -> do
        e' <- go
        WB.insertIdxValue cache idx e'
        return e'
    Nothing -> go
  where
    go :: IO (WB.Expr t tp)
    go = case e of
      WB.AppExpr appExpr -> do
        let ap = WB.appExprApp appExpr
        ap' <- WB.traverseApp (normFieldAccs sym cache) ap
        let ret = if ap == ap' then return e else WB.sbMakeExpr sym ap'
        goApp ret ap'
      WB.NonceAppExpr nae ->
        case WB.nonceExprApp nae of
          WB.FnApp symFn args -> do
            args' <- FC.traverseFC (normFieldAccs sym cache) args
            case (args' == args) of
              True -> return e
              False -> WI.applySymFn sym symFn args'
          _ -> return e
      _ -> return e

    goApp :: IO (WB.Expr t tp) -> WB.App (WB.Expr t) tp -> IO (WB.Expr t tp)
    goApp ret ap = case ap of
      (WB.StructCtor _ flds) -> do
        flds' <- Ctx.traverseWithIndex (\idx _ -> normField sym cache e idx) flds
        case flds' == flds of
          True -> ret
          False -> WI.mkStruct sym flds'
      (WB.StructField e' idx _) -> do
        fld <- normField sym cache e' idx
        normFieldAccs sym cache fld
      _ -> ret

normField :: forall sym st fs t ctx tp
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> WB.IdxCache t (WB.Expr t)
          -> WB.Expr t (WI.BaseStructType ctx)
          -> Ctx.Index ctx tp
          -> IO (WB.Expr t tp)
normField sym cache e idx = case e of
  WB.AppExpr appExpr' -> case (WB.appExprApp appExpr') of
    WB.StructField e' idx' _  -> do
      e'' <- normFieldAccs sym cache e'
      fld <- normField sym cache e'' idx'
      normField sym cache fld idx

    WB.StructCtor _ flds -> normFieldAccs sym cache $ flds Ctx.! idx
    WB.BaseIte _ _ test then_ else_ -> do
      test' <- normFieldAccs sym cache test
      then' <- normField sym cache then_ idx
      else' <- normField sym cache else_ idx
      WI.baseTypeIte sym test' then' else'
    _ -> fail $ "Failed to fully normalize struct access: \n" ++ showExpr e
  _ -> fail $ "Failed to fully normalize struct access: \n" ++ showExpr e


data BVExpr t n where
  BVExpr :: 1 <= n => WB.Expr t (WI.BaseBVType n) -> BVExpr t n

instance Show (BVExpr t n) where
  show (BVExpr e) = showExpr e

instance ShowF (BVExpr t) where
  showF (BVExpr e) = showExpr e

bvSize :: WB.Expr t (WI.BaseBVType n) -> NR.NatRepr n
bvSize e = case WI.exprType e of
  WI.BaseBVRepr sz -> sz

bvExpr :: BVExpr t n -> WB.Expr t (WI.BaseBVType n)
bvExpr (BVExpr e) = e

bvSize' :: BVExpr t n -> NR.NatRepr n
bvSize' (BVExpr e) = bvSize e

withBVSize :: WB.Expr t (WI.BaseBVType n) -> (1 NR.<= n => f) -> f
withBVSize e f = case WI.exprType e of
    WI.BaseBVRepr _ -> f

matchSizes' :: forall sym st fs t n n'
            . sym ~ WB.ExprBuilder t st fs
           => sym
           -> WB.Expr t (WI.BaseBVType n)
           -> WB.Expr t (WI.BaseBVType n')
           -> IO (Pair (BVExpr t) (BVExpr t))
matchSizes' sym e1 e2 = withBVSize e1 $ withBVSize e2 $ case NR.testNatCases (bvSize e1) (bvSize e2) of
  NR.NatCaseLT NR.LeqProof -> do
    e1' <- WI.bvSext sym (bvSize e2) e1
    return $ Pair (BVExpr e1') (BVExpr e2)
  NR.NatCaseGT NR.LeqProof -> do
    e2' <- WI.bvSext sym (bvSize e1) e2
    return $ Pair (BVExpr e1) (BVExpr e2')
  NR.NatCaseEQ -> return $ Pair (BVExpr e1) (BVExpr e2)

extendToS :: forall sym st fs t maxn n
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> NR.NatRepr maxn
          -> WB.Expr t (WI.BaseBVType n)
          -> IO (WB.Expr t (WI.BaseBVType maxn))
extendToS sym nr e  = withBVSize e $ case NR.testNatCases (bvSize e) nr of
  NR.NatCaseLT NR.LeqProof -> WI.bvSext sym nr e
  NR.NatCaseGT _ -> fail $ "computed size is too small: Target size " ++ show nr ++ " vs actual size:" ++ show (bvSize e) ++ " in expression " ++ showExpr e
  NR.NatCaseEQ -> return $ e

-- | Either sign-extend or truncate a bitvector to the given width.
matchSizeToS :: forall sym st fs t n' n
              . sym ~ WB.ExprBuilder t st fs
             => 1 <= n
             => sym
             -> NR.NatRepr n
             -> WB.Expr t (WI.BaseBVType n')
             -> IO (WB.Expr t (WI.BaseBVType n))
matchSizeToS sym nr e = withBVSize e $ case NR.testNatCases (bvSize e) nr of
  NR.NatCaseLT NR.LeqProof -> WI.bvSext sym nr e
  NR.NatCaseGT NR.LeqProof -> WI.bvTrunc sym nr e
  NR.NatCaseEQ -> return $ e



-- | Either zero-extend or truncate a bitvector to the given width.
matchSizeToU :: forall sym st fs t n' n
              . sym ~ WB.ExprBuilder t st fs
             => 1 <= n
             => sym
             -> NR.NatRepr n
             -> WB.Expr t (WI.BaseBVType n')
             -> IO (WB.Expr t (WI.BaseBVType n))
matchSizeToU sym nr e = withBVSize e $ case NR.testNatCases (bvSize e) nr of
  NR.NatCaseLT NR.LeqProof -> WI.bvZext sym nr e
  NR.NatCaseGT NR.LeqProof -> WI.bvTrunc sym nr e
  NR.NatCaseEQ -> return $ e

data WrapInt f g tp where
  WrapIntSimple :: f tp -> g tp -> WrapInt f g tp
  WrapIntInt :: f (WI.BaseBVType n) -> g WI.BaseIntegerType -> WrapInt f g WI.BaseIntegerType

unwrapInt :: WrapInt f g tp -> g tp
unwrapInt wi = case wi of
  WrapIntSimple _ g -> g
  WrapIntInt _ g -> g

-- | Given an expression containing a set of bound variables and target bindings, rewrite the
-- expression to contain no integers in any sub-terms, and return a fresh set of bindings for
-- the given variables. Non-integer variables are unchanged, while integer variables are re-assigned
-- to a variable of some bitvector length (based on constraints present in the term), and their
-- corresponding expression is rebound to a signed-conversion of the original.
--
-- e.g.
-- Environment: ?int1 <-> field 0 ?struct, ?int2 <-> field 1 ?struct
-- Expression: SInt(?int1) > Zeros(32) AND SInt(?int2) > Zeros(64)
-- ===>
-- Environment: ?bv1 :: bv(32) <-> sbvTointeger(field 0 ?struct), ?bv2 :: bv(64) <-> sbvToInteger(field 1 ?struct)
-- Expression: ?bv1 > Zeros(32) AND ?bv2 > Zeros(64)
extractIntBVs :: forall t ctx tp
               . Ctx.Assignment (WB.ExprBoundVar t) ctx
              -> Ctx.Assignment (WB.Expr t) ctx
              -> WB.Expr t tp
              -> RebindM t (WB.Expr t tp, Pair (Ctx.Assignment (WB.ExprBoundVar t)) (Ctx.Assignment (WB.Expr t)))
extractIntBVs subbvs argExprs expr = do
  wrappedInts <- FC.traverseFC refreshIntVar subbvs
  bvarsToIntExprs <- return $ FC.fmapFC unwrapInt wrappedInts
  expr' <- withSym $ \sym -> WB.evalBoundVars sym expr subbvs bvarsToIntExprs
  expr'' <- extractInts expr'
  argExprPairs <- Ctx.zipWithM refreshIntArg argExprs wrappedInts
  Some asns <- return $ Ctx.fromList $ FC.toListFC (\(Const c) -> c) $ argExprPairs
  (newVars, newArgs) <- return $ unzipPairF asns
  return $ (expr'', Pair newVars newArgs)
  where
    refreshIntArg :: forall tp'. WB.Expr t tp'
                  -> WrapInt (WB.ExprBoundVar t) (WB.Expr t) tp'
                  -> RebindM t (Const (Some (PairF (WB.ExprBoundVar t) (WB.Expr t))) tp')
    refreshIntArg argExpr wi = case wi of
      WrapIntInt bv _ -> do
        WI.BaseBVRepr n <- withSym $ \sym -> return $ WI.exprType (WI.varExpr sym bv)
        argExpr' <- integerToSBV argExpr n
        return $ Const $ Some $ PairF bv argExpr'
      WrapIntSimple bv _ -> return $ Const $ Some $ PairF bv argExpr

    refreshIntVar :: forall tp'. WB.ExprBoundVar t tp'
                  -> RebindM t (WrapInt (WB.ExprBoundVar t) (WB.Expr t) tp')
    refreshIntVar bv = do
      intBounds <- MS.gets rbBVMap
      case WB.bvarType bv of
        WI.BaseIntegerRepr -> case Map.lookup bv intBounds of
            Just (BVBound n) -> do
              bv_var <- withSym $ \sym -> WI.freshBoundVar sym (appendToSymbol (WB.bvarName bv) "_asBVar") (WI.BaseBVRepr n)
              expr' <- withSym $ \sym -> WI.sbvToInteger sym (WI.varExpr sym bv_var)
              return $ WrapIntInt bv_var expr'
            Just (BVUnbounded) -> withSym $ \sym -> return $ WrapIntSimple bv (WI.varExpr sym bv)
            _ -> fail $ "Missing bounds for integer variable:"
                   ++ show bv ++ " with bounds: " ++ show intBounds
                   ++ " in expression: \n" ++ showExpr expr
        _ -> withSym $ \sym -> return $ WrapIntSimple bv (WI.varExpr sym bv)

-- | If the expression is a bitvector, set the bound to its width. Otherwise leave it unchanged.
withExprBound :: WB.Expr t tp -> RebindM t a -> RebindM t a
withExprBound e f = case WI.exprType e of
  WI.BaseBVRepr _ -> withBVBounds e f
  _ -> f

mkUF :: String
     -> Ctx.Assignment WI.BaseTypeRepr args
     -> WI.BaseTypeRepr ret
     -> RebindM t (WB.ExprSymFn t args ret)
mkUF nm args ret = do
  fnCache <- MS.gets rbFnCache
  case Map.lookup nm fnCache of
    Just (SomeSome symFn)
      | Just Refl <- testEquality (WI.fnArgTypes symFn) args
      , Just Refl <- testEquality (WI.fnReturnType symFn) ret
      -> return symFn
    _ -> do
      symFn <- withSym $ \sym -> do
        WI.freshTotalUninterpFn sym (WI.safeSymbol nm) args ret
      MS.modify $ \st -> st { rbFnCache = Map.insert nm (SomeSome symFn) (rbFnCache st) }
      return symFn

integerToSBV :: forall t n
              . 1 <= n
             => WB.Expr t WI.BaseIntegerType
             -> NR.NatRepr n
             -> RebindM t (WB.Expr t (WI.BaseBVType n))
integerToSBV e n = do
  let nm = "integerToSBV_" ++ show (NR.intValue n)
  let args = Ctx.empty Ctx.:> WI.BaseIntegerRepr
  let ret = WI.BaseBVRepr n
  symFn <- mkUF nm args ret
  withSym $ \sym -> WI.applySymFn sym symFn (Ctx.singleton e)


safeTruncate :: forall t n' n
              . 1 <= n
             => WB.Expr t (WI.BaseBVType n')
             -> NR.NatRepr n
             -> RebindM t (WB.Expr t (WI.BaseBVType n))
safeTruncate e n = do
  WI.BaseBVRepr n' <- return $ WI.exprType e
  let nm = "safeTruncate_" ++ show (NR.intValue n') ++ "_" ++ show (NR.intValue n)
  let args = Ctx.empty Ctx.:> WI.BaseBVRepr n'
  let ret = WI.BaseBVRepr n
  fnName <- MR.asks rbFunName
  IO.liftIO $ putStrLn $ T.unpack fnName ++ ": Using safeTruncate to truncate from " ++ show n' ++ " down to " ++ show n ++ " bits."
  symFn <- mkUF nm args ret
  withSym $ \sym -> WI.applySymFn sym symFn (Ctx.singleton e)

data BVOp t where
  BVOp :: (forall n
        . 1 <= n
       => WB.Expr t (WI.BaseBVType n)
       -> WB.Expr t (WI.BaseBVType n)
       -> RebindM t (WB.Expr t (WI.BaseBVType n)))
       -> BVOp t

asBVOp :: WB.Expr t (WI.BaseBVType n)
       -> Maybe ( WB.Expr t (WI.BaseBVType n)
                , WB.Expr t (WI.BaseBVType n)
                , BVOp t)
asBVOp expr = case WB.asApp expr of
  Just (WB.BVLshr _ bv1 bv2) -> Just (bv1, bv2, BVOp $ \bv1' bv2' -> withSym $ \sym -> WI.bvLshr sym bv1' bv2')
  Just (WB.BVShl _ bv1 bv2) -> Just (bv1, bv2, BVOp $ \bv1' bv2' -> withSym $ \sym -> WI.bvShl sym bv1' bv2')
  -- Just (WB.SemiRingProd sm)
  --   | WI.SemiRingBVRepr WI.BVBitsRepr _ <- WSum.prodRepr sm
  --   , Just [bv1, bv2] <- WSum.prodEval (++) (\e -> [e]) sm
  --   -> Just (bv1, bv2, BVOp $ \bv1' bv2' -> withSym $ \sym -> WI.bvAndBits sym bv1' bv2')
  _ -> Nothing

-- | Traverse an expression and extract all integer sub-terms by rewriting
-- them as equivalent bitvector operations.
-- The resulting expression is in "Integer-normal form" where all integer subterms
-- are the result of some "bvToInteger" or "sbvToInteger" operation.
extractInts' :: forall t tp
              . WB.Expr t tp
             -> RebindM t (WB.Expr t tp)
extractInts' expr =  withExpr "extractInts'" expr $ do
  case expr of
    -- special case where a bitvector binary operation has simply been lifted
    -- over two integers. In this case we actually don't care about the bounds
    -- of the original bitvector, and instead extract each inner int
    -- under the current bounds.

    _ | Just (Some (BVExpr bv), Refl) <- asSBVToInteger expr
      , Just (bv1, bv2, BVOp bvOp) <- asBVOp bv
      , Just (int1, _) <- asIntegerToSBV bv1
      , Just (int2, _) <- asIntegerToSBV bv2 -> do
          Some bv1' <- extractBitV int1
          Some bv2' <- extractBitV int2
          Pair (BVExpr bv1'') (BVExpr bv2'') <- matchSizes bv1' bv2'
          result <- bvOp bv1'' bv2''
          withSym $ \sym -> WI.sbvToInteger sym result

    _ | Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg)) <- asSymFn (\nm -> nm == "extractBitVinttobv") expr
      , WI.BaseIntegerRepr <- WI.exprType arg -> case arg of
          WB.BoundVarExpr bv -> do
            updateBoundOf bv
            getUpperBoundOf bv >>= \case
              BVUnbounded -> do
                bvExpr <- withSym $ \sym -> return $ WI.varExpr sym bv
                ME.throwError (UnboundedInteger bvExpr)
              _ -> return expr
          _ -> return expr

    _ | Just (expr', AsBVRepr sz) <- asIntegerToSBV expr -> do
          Some (BVExpr bv) <- extractBitV expr'
          withSym $ \sym -> extendToS sym sz bv

    _ | Just (expr', AsBVRepr sz) <- asIntegerToSBVNoBound expr -> do
          withNoBound $ do
            Some (BVExpr bv) <- extractBitV expr'
            WI.BaseBVRepr sz <- return $ WI.exprType expr
            withSym $ \sym -> matchSizeToS sym sz bv

    WB.AppExpr appExpr -> do
      expr' <- go $! WB.appExprApp appExpr
      return $! expr'

    WB.NonceAppExpr nae ->
      case WB.nonceExprApp nae of
        WB.FnApp symFn args -> do
          args' <- FC.traverseFC (extractInts) args
          if (args == args') then
            return expr
          else
            withSym $ \sym -> WI.applySymFn sym symFn args'
    _ -> return expr

  where
    -- The bitvectors backing each integer need an extra signed bit (above what
    -- would be strictly required by a given IntegerToBV wrapper) so that we
    -- may unambiguously treat all bitvector-backed integers as signed bitvectors.
    --
    -- for example, given:
    -- if (n > -1)
    -- then IntegerToBV (n) [4]
    --
    -- if we back 'n' by a bitvector of only size 4 then we get
    -- if (n > '1111')
    -- then n
    --
    -- Which does not result in the desired behavior for any n > 7 (with signed
    -- comparison), as n will erroneously be interpeted as a negative number.
    -- We therefore extract these integers with a bounds of size+1 for any
    -- IntegerToBV context, and truncate the sign bit to get the expected result.
    -- e.g.:
    -- if (n > '11111')
    -- then (bvTrunc (4, n))

    normBinOp :: forall tp' tp'' n
               . WB.Expr t tp'
              -> WB.Expr t tp''
              -> (forall st fs. WB.ExprBuilder t st fs -> WB.Expr t tp' -> WB.Expr t tp'' -> IO (WB.Expr t tp))
              -> RebindM t (WB.Expr t tp)
    normBinOp e1 e2 f =  do
      e1' <- extractInts e1
      e2' <- extractInts e2
      if (e1' == e1 && e2 == e2') then
        return expr
      else
        withSym $ \sym -> f sym e1' e2'

    normUnOp :: forall tp' n
              . WB.Expr t tp'
             -> (forall st fs. WB.ExprBuilder t st fs -> WB.Expr t tp' -> IO (WB.Expr t tp))
             -> RebindM t (WB.Expr t tp)
    normUnOp e f = do
      e' <- extractInts e
      if (e' == e) then
        return expr
      else
        withSym $ \sym -> f sym e'

    go :: WB.App (WB.Expr t) tp -> RebindM t (WB.Expr t tp)
    go (WB.BVToInteger bv) = normUnOp bv $ WI.bvToInteger
    go (WB.SBVToInteger bv) = normUnOp bv $ WI.sbvToInteger

    go (WB.BVShl _ e1 e2) = normBinOp e1 e2 WI.bvShl
    go (WB.BVUdiv _ e1 e2) = normBinOp e1 e2 WI.bvUdiv
    go (WB.BVSdiv _ e1 e2) = normBinOp e1 e2 WI.bvSdiv
    go (WB.BVLshr _ e1 e2) = normBinOp e1 e2 WI.bvLshr
    go (WB.BVAshr _ e1 e2) = normBinOp e1 e2 WI.bvAshr
    go (WB.BVZext sz e) = normUnOp e (\sym -> WI.bvZext sym sz)
    go (WB.BVSext sz e) = normUnOp e (\sym -> WI.bvSext sym sz)
    go (WB.BVSelect idx sz e) = withBVBounds e $ normUnOp e (\sym -> WI.bvSelect sym idx sz)
    go (WB.BVConcat _ e1 e2) = do
      e1' <- withBVBounds e1 $ extractInts e1
      e2' <- withBVBounds e2 $ extractInts e2
      withSym $ \sym -> WI.bvConcat sym e1' e2'

    go (WB.NotPred e) = normUnOp e WI.notPred

    go (WB.BaseIte _ _ test then_ else_) = do
      test' <- withNoBound $ extractInts test
      then' <- extractInts then_
      else' <- extractInts else_
      if (test == test' && then_ == then' && else_ == else') then
        return expr
      else
        withSym $ \sym -> WI.baseTypeIte sym test' then' else'

    go (WB.BVOrBits sz ors) = do
      ors' <- WB.traverseBVOrSet extractInts ors
      withSym $ \sym -> WB.sbMakeExpr sym (WB.BVOrBits sz ors')

    go (WB.BaseEq tp a1 b1) = withNoBound $ case tp of
        WI.BaseIntegerRepr -> do
          Some a2 <- extractBitV a1
          Some b2 <- extractBitV b1
          Pair (BVExpr a3) (BVExpr b3) <- matchSizes a2 b2
          withSym $ \sym -> WI.isEq sym a3 b3
        _  -> normBinOp a1 b1 WI.isEq

    go (WB.ConjPred bm) = withNoBound $ do
      bm' <- BM.traverseVars extractInts bm
      withSym $ \sym -> WB.sbMakeExpr sym (WB.ConjPred bm')

    go (WB.SemiRingSum sm) = case WI.exprType expr of
      WI.BaseIntegerRepr -> return expr
      _ -> do
        sm' <- WSum.traverseVars extractInts sm
        withSym $ \sym -> WB.sbMakeExpr sym (WB.SemiRingSum sm')

    go (WB.SemiRingProd sp) = case WI.exprType expr of
      WI.BaseIntegerRepr -> return expr
      _ -> do
        sp' <- WSum.traverseProdVars extractInts sp
        withSym $ \sym -> WB.sbMakeExpr sym (WB.SemiRingProd sp')

    go (WB.SemiRingLe sl a1 b1) = withNoBound $ do
      case sl of
        WI.OrderedSemiRingIntegerRepr -> do
          Some a2 <- extractBitV a1
          Some b2 <- extractBitV b1
          Pair (BVExpr a3) (BVExpr b3) <- matchSizes a2 b2
          eqPred <- withSym $ \sym -> WI.isEq sym a3 b3
          ltPred <- withSym $ \sym -> WI.bvSlt sym a3 b3
          withSym $ \sym -> WI.orPred sym eqPred ltPred
        _ -> return expr

    go (WB.StructField e idx _) = normUnOp e $ (\sym e' -> WI.structField sym e' idx)

    go (WB.StructCtor _ flds) = withNoBound $ do
      flds' <- FC.traverseFC extractInts flds
      withSym $ \sym -> WI.mkStruct sym flds'

    go _ = return expr

data SomeSymFn t tp where
  SomeSymFn :: WB.ExprSymFn t args tp -> Ctx.Assignment (WB.Expr t) args -> SomeSymFn t tp

data AsBVRepr tp where
  AsBVRepr :: 1 <= n => NR.NatRepr n -> AsBVRepr (WI.BaseBVType n)

asSymFn :: (T.Text -> Bool) -> WB.Expr t tp -> Maybe (SomeSymFn t tp)
asSymFn f e = case e of
  WB.NonceAppExpr nae ->
    case WB.nonceExprApp nae of
      WB.FnApp symFn args | f (WI.solverSymbolAsText $ WB.symFnName symFn) -> return $ SomeSymFn symFn args
      _ -> fail ""
  _ -> fail ""

asUNDEFINEDInt :: WB.Expr t WI.BaseIntegerType
               -> Maybe (WB.Expr t WI.BaseIntegerType)
asUNDEFINEDInt expr = do
  SomeSymFn _ args <- asSymFn (\nm -> nm == "UNDEFINED_integer") expr
  case args of
    Ctx.Empty -> return expr
    _ -> fail ""

asSBVToInteger :: WB.Expr t tp
               -> Maybe (Some (BVExpr t), tp :~: WI.BaseIntegerType)
asSBVToInteger expr = case asSymFn (\nm -> "sbvToInteger_" `T.isPrefixOf` nm) expr of
  Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg))
    | WI.BaseBVRepr n <- WI.exprType arg
    , WI.BaseIntegerRepr <- WI.exprType expr -> return $ (Some $ BVExpr arg, Refl)
  _ -> case WB.asApp expr of
    Just (WB.SBVToInteger e) -> return (Some $ BVExpr e, Refl)
    _ -> fail ""

asIntegerToSBV' :: (T.Text -> Bool)
               -> WB.Expr t tp
               -> Maybe (WB.Expr t WI.BaseIntegerType, AsBVRepr tp)
asIntegerToSBV' f expr = case asSymFn f expr of
  Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg))
    | WI.BaseIntegerRepr <- WI.exprType arg
    , WI.BaseBVRepr n <- WI.exprType expr -> return $ (arg, AsBVRepr (bvSize expr))
  Nothing -> fail ""

asIntegerToSBV :: WB.Expr t tp
               -> Maybe (WB.Expr t WI.BaseIntegerType, AsBVRepr tp)
asIntegerToSBV expr = case asIntegerToSBV' (\nm -> "uf_integerToSBV_" `T.isPrefixOf` nm) expr of
  Just result -> return result
  _ -> case WB.asApp expr of
    Just (WB.IntegerToBV ie sz) -> return $ (ie, AsBVRepr sz)
    _ -> fail ""

asIntegerToSBVNoBound :: WB.Expr t tp
                     -> Maybe (WB.Expr t WI.BaseIntegerType, AsBVRepr tp)
asIntegerToSBVNoBound = asIntegerToSBV' (\nm -> "uf_integerToSBVNoBound_" `T.isPrefixOf` nm)


exprIsVar :: WB.Expr t tp -> Bool
exprIsVar e = case e of
  WB.BoundVarExpr _ -> True
  _ -> False

intIsBound :: Ctx.Assignment (WB.Expr t) (Ctx.EmptyCtx Ctx.::> WI.BaseIntegerType)
          -> Bool
intIsBound (Ctx.Empty Ctx.:> e) = not $ exprIsVar e

-- | Extract a bitvector from an integer expression, assuming it is already
-- in normal form.
extractBitV' :: forall t
              . WB.Expr t WI.BaseIntegerType
             -> RebindM t (Some (BVExpr t))
extractBitV' expr = withExpr "extractBitV'" expr $ do
  case expr of
    WB.AppExpr appExpr -> do
      expr' <- go $! WB.appExprApp appExpr
      return $! expr'
    WB.BoundVarExpr bv -> do
      updateBoundOf bv
      getUpperBoundOf bv >>= \case
        BVBound n -> do
          e <- withSym $ \sym -> do
            freshIntBV <- WI.freshBoundVar sym WI.emptySymbol WI.BaseIntegerRepr
            fnBody <- WI.integerToBV sym (WI.varExpr sym freshIntBV) n
            fn <- WI.definedFn sym
                    (WI.safeSymbol "extractBitVinttobv")
                    (Ctx.empty Ctx.:> freshIntBV)
                    fnBody
                    intIsBound
            WI.applySymFn sym fn (Ctx.empty Ctx.:> expr)
          mkSomeBV e
        BVUnbounded -> ME.throwError (UnboundedInteger expr)

    _ | Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg)) <- asSymFn (\nm -> nm == "extractBitVinttobv") expr
      , Just (Some (BVExpr bv), _) <- asSBVToInteger arg -> do
           bv' <- extractInts bv
           mkSomeBV bv'

    _ | Just (Some (BVExpr bv), _) <- asSBVToInteger expr -> do
          bv' <- extractInts bv
          mkSomeBV bv'
    _ | Just _ <- asUNDEFINEDInt expr -> do
           getUpperBound >>= \case
             BVBound n -> do
               bv <- withSym $ \sym -> do
                 fn <- WI.freshTotalUninterpFn sym (WI.safeSymbol ("UNDEFINED_bitvector_" ++ show n)) Ctx.empty (WI.BaseBVRepr n)
                 WI.applySymFn sym fn Ctx.empty
               mkSomeBV bv
             BVUnbounded -> ME.throwError (UnboundedInteger expr)

    _ -> case WI.asInteger expr of
      Just i -> mkSomeLitSBV i
      _ -> fail $ "extractBitV: unsupported expression shape: " ++ showExpr expr
  where
    liftBinop :: WB.Expr t WI.BaseIntegerType
              -> WB.Expr t WI.BaseIntegerType
              -> (forall n st fs
                   . 1 <= n
                  => WB.ExprBuilder t st fs
                  -> WB.Expr t (WI.BaseBVType n)
                  -> WB.Expr t (WI.BaseBVType n)
                  -> IO (WB.Expr t (WI.BaseBVType n)))
              -> RebindM t (Some (BVExpr t))
    liftBinop a1 b1 f = do
      Some a2 <- extractBitV a1
      Some b2 <- extractBitV b1
      Pair (BVExpr a3) (BVExpr b3) <- matchSizes a2 b2
      result <- withSym $ \sym -> f sym a3 b3
      mkSomeBV result

    go :: WB.App (WB.Expr t) WI.BaseIntegerType -> RebindM t (Some (BVExpr t))

    -- to unambiguously treat all bitvector-backed integers as signed, we need to zero-extend any
    -- BVToInteger so that the sign bit is always correct.
    go (WB.BVToInteger bv) = do
      bv' <- withSym $ \sym -> WI.bvZext sym (NR.incNat (bvSize bv)) bv
      mkSomeBV bv'
    go (WB.SBVToInteger bv) = mkSomeBV bv
    go (WB.BaseIte _ _ test then_ else_) = liftBinop then_ else_ (\sym -> WI.baseTypeIte sym test)

    go (WB.IntMod a1 b1)
      | Just b2 <- WI.asInteger b1
      , b2 >= 2 = do
          Some a2 <- withNoBound $ extractBitV a1
          Some (BVExpr b3) <- mkSomeLitSBV b2
          Pair (BVExpr a3) (BVExpr b4) <- matchSizes a2 (BVExpr b3)
          withSym $ \sym -> do
            result <- WI.bvSrem sym a3 b4
            nr <- return $ NR.decNat (bvSize b3)
            Just NR.LeqProof <- return $ NR.isPosNat nr
            (Some . BVExpr) <$> matchSizeToS sym nr result

    go (WB.IntDiv a1 b1)
      | Just b2 <- WI.asInteger b1
      , b2 >= 2 = do
          Some (BVExpr b3) <- mkSomeLitSBV b2
          Some a2 <- restoreBounds $ do
            increaseBoundBy (bvSize b3)
            extractBitV a1
          Pair (BVExpr a3) (BVExpr b4) <- matchSizes a2 (BVExpr b3)
          result <- withSym $ \sym -> WI.bvSdiv sym a3 b4
          truncateToBound result

    go (WB.IntMod a1 b1) = liftBinop a1 b1 WI.bvSrem
    go (WB.IntDiv a1 b1) = liftBinop a1 b1 WI.bvSdiv
    go (WB.IntAbs e1) = do
      e2 <- withSym $ \sym -> do
        negone <- WI.intLit sym (-1)
        zero_ <- WI.intLit sym 0
        isPos <- WI.intLe sym zero_ e1
        nege1 <- WI.intMul sym negone e1
        WI.baseTypeIte sym isPos e1 nege1
      extractBitV e2

    -- for arithmetic, we need to incrementally reduce the bounds when extracting
    -- each component in order to ensure that we have enough available bits in
    -- the outer expression to compute the result without the risk of overflow


    -- for multiplication, we require the sum of the number of bits in both terms.
    -- for example, given i * j * k under a 32-bit bound, we first compute the number
    -- of bits required to represent k as M, and then calculate the bits required for (i * j) under
    -- a bound of 32 - M.
    go (WB.SemiRingProd pd) =
      case WSum.prodRepr pd of
        WI.SemiRingIntegerRepr -> do
          let
            smul :: WB.Expr t WI.BaseIntegerType
                 -> WB.Expr t WI.BaseIntegerType
                 -> RebindM t (WB.Expr t WI.BaseIntegerType)
            smul a1 b1 = do
              Some b1_bv_unbounded <- extractBitV b1
              Some a2 <- restoreBounds $ do
                reduceBoundForIntMul b1_bv_unbounded
                extractBitV a1
              Some b2 <- restoreBounds $ do
                reduceBoundForIntMul a2
                extractBitV b1
              Some (BVExpr result) <- bvMul a2 b2
              withSym $ \sym -> WI.sbvToInteger sym result


          Just result <- WSum.prodEvalM smul return pd
          extractBitV result

    -- for addition, we require one extra bit for each additional term
    -- for example, given i + j + k under a 32-bit bound, we require i, j and k to
    -- be representable with 30 bits each.

    go (WB.SemiRingSum sm) =
      case WSum.sumRepr sm of
        WI.SemiRingIntegerRepr -> do
          sumBounds <- restoreBounds $ do
            incBound
            WSum.evalM (\_ _ -> return ()) (\_ _  -> decBound) (\_ -> decBound) sm
            getBounds
          let
            mkBV coef_int expr_int = withExpr ("extractBitV: sum: " ++ show sumBounds) expr_int $ withBounds sumBounds $ do
              Some coef_bv <- mkSomeLitSBV coef_int
              Some expr_bv <- restoreBounds $ do
                reduceBoundForIntMul coef_bv
                extractBitV expr_int
              bvMul coef_bv expr_bv

          WSum.evalM (\(Some e1) (Some e2) -> bvAdd e1 e2) mkBV mkSomeLitSBV sm

    go _ = fail $ "extractBitV: unsupported expression shape: " ++ showExpr expr

reduceBoundForIntMul :: BVExpr t n
                     -> RebindM t ()
reduceBoundForIntMul (BVExpr e) = withExpr "reduceBoundForIntMul: " e $ case WI.asSignedBV e of
  Just 0 -> return ()
  Just 1 -> return ()
  Just (-1) -> return ()
  Just 2 -> reduceBoundBy (NR.knownNat @1)
  _ -> withBVSize e $ reduceBoundBy (NR.decNat $ bvSize e)


increaseBoundBy :: NR.NatRepr n
                -> RebindM t ()
increaseBoundBy n = getBounds >>= \case
  BVUnbounded -> return ()
  BVBound maxn -> do
    bnd <- mkBound (maxn `NR.addNat` n)
    setBound bnd

reduceBoundBy :: NR.NatRepr n
              -> RebindM t ()
reduceBoundBy n = getBounds >>= \case
  BVUnbounded -> return ()
  BVBound maxn -> case NR.testLeq n maxn of
    Just NR.LeqProof -> do
      bnd <- mkBound $ maxn `NR.subNat` n
      setBound bnd
    Nothing -> fail $ "reduceBoundBy: cannot reduce current bound of " ++ show maxn ++ " by " ++ show n

-- | bits (N) + bits(M) = bits(max(N,M) + 1)
bvAdd :: forall t n n'
       . BVExpr t n
      -> BVExpr t n'
      -> RebindM t (Some (BVExpr t))
bvAdd (BVExpr a1) (BVExpr b1) = withExpr "bvAdd1" a1 $ withExpr "bvAdd2" b1 $ do
  Some maxsz <- return $ NR.maxNat (bvSize a1) (bvSize b1)
  let sz = NR.incNat maxsz
  (Some (BVExpr result) :: Some (BVExpr t)) <- withSym $ \sym -> do
    a2 <- extendToS sym sz a1
    b2 <- extendToS sym sz b1
    Just NR.LeqProof <- return $ NR.isPosNat sz
    (Some . BVExpr) <$> WI.bvAdd sym a2 b2
  mkSomeBV result


-- | bits(N) * bits(M) = bits(N+M)
-- Assuming the bitvector is already a signed representation of an integer, -1 and 1 do not affect the
-- bit requirement.
bvMul :: forall t n n'
       . BVExpr t n
      -> BVExpr t n'
      -> RebindM t (Some (BVExpr t))
bvMul (BVExpr a1) (BVExpr b1) =
  case (WI.asSignedBV a1, WI.asSignedBV b1) of
    (Just a2, Just b2) -> mkSomeLitSBV (a2 * b2)
    (Just 1, Nothing) -> mkSomeBV b1
    (Nothing, Just 1) -> mkSomeBV a1
    (Just 2, Nothing) -> bvAdd (BVExpr b1) (BVExpr b1)
    (Nothing, Just 2) -> bvAdd (BVExpr a1) (BVExpr a1)
    (Just (-1), Nothing) -> Some <$> neg (BVExpr b1)
    (Nothing, Just (-1)) -> Some <$> neg (BVExpr a1)
    _ -> do
      let sz = NR.addNat (bvSize a1) (bvSize b1)
      BVExpr result :: BVExpr t (n + n') <- withSym $ \sym -> do
        a2 <- extendToS sym sz a1
        b2 <- extendToS sym sz b1
        pos_bv <- return $ NR.leqProof (NR.knownNat @1) (bvSize a1)
        pos_coef <- return $ NR.leqProof (NR.knownNat @1) (bvSize b1)
        NR.LeqProof <- return $ NR.leqAdd pos_bv (bvSize b1)
        BVExpr <$> WI.bvMul sym a2 b2
      mkSomeBV result
  where
    neg :: forall n''. BVExpr t n'' -> RebindM t (BVExpr t n'')
    neg (BVExpr e) = withSym $ \sym -> do
      negone <- WI.bvLit sym (bvSize e) (-1)
      BVExpr <$> WI.bvMul sym negone e

incSize :: forall sym st fs t n n'
         . sym ~ WB.ExprBuilder t st fs
        => sym
        -> BVExpr t n
        -> RebindM t (BVExpr t (n + 1))
incSize sym (BVExpr e)
  | NR.LeqProof <- NR.leqAdd (NR.leqProof (NR.knownNat @1) (bvSize e)) (NR.knownNat @1)
  = BVExpr <$> (IO.liftIO $ extendToS sym (NR.incNat (bvSize e)) e)

data BVVar t n where
  BVVar :: 1 <= n => WB.ExprBoundVar t (WI.BaseBVType n) -> BVVar t n

deriving instance (Show (BVVar t n))

instance ShowF (BVVar t) where
  showF bv = show bv

data BVBound where
  BVBound :: 1 <= n => NR.NatRepr n -> BVBound
  BVUnbounded :: BVBound

deriving instance Show BVBound

instance Eq BVBound where
  bnd1 == bnd2 = case (bnd1, bnd2) of
    (BVBound n1, BVBound n2) | Just Refl <- testEquality n1 n2 -> True
    (BVUnbounded, BVUnbounded) -> True
    _ -> False

instance Ord BVBound where
  compare bnd1 bnd2 = case (bnd1, bnd2) of
    (BVBound n1, BVBound n2) -> toOrdering $ compareF n1 n2
    (BVUnbounded, BVUnbounded) -> EQ
    (BVBound _, BVUnbounded) -> LT
    (BVUnbounded, BVBound _) -> GT

data ExprPath t where
  ExprPath :: [(Some (WB.Expr t), BVBound, String)] -> Set (Some (WB.Expr t)) -> ExprPath t

emptyExprPath :: ExprPath t
emptyExprPath = ExprPath [] Set.empty

addToPath :: String -> WB.Expr t tp -> BVBound -> ExprPath t -> ExprPath t
addToPath msg e bnd (ExprPath p s) = ExprPath ((Some e, bnd, msg) : p) (Set.insert (Some e) s)

data RebindEnv t where
  RebindEnv :: { rbBuilder :: WB.ExprBuilder t st fs
               -- ^ underlying expression builder for constructing new terms,
               -- access via 'withSym'
               , rbDefaultMaxBV :: Maybe BVBound
               -- ^ a concrete max bound for assigning widths to fresh bitvectors backing
               -- integers which do not have any bounds information
               , rbPath :: ExprPath t
               -- ^ the current traversal path of the normalization
               -- Used for providing context to error messages
               , rbFunName :: T.Text
               -- ^ name of the top-level function being normalized
               , rbTruncateOverflow :: Bool
               } -> RebindEnv t

data RebindState t =
  RebindState { rbBVMap :: Map (WB.ExprBoundVar t WI.BaseIntegerType) BVBound
              -- ^ establishing a maximum bound for the bitvector backing each integer-type bound variable.
              , rbCurrentBound :: BVBound
              -- ^ the maximum bound for any fresh bitvectors generated from converting integers
              , rbNormFieldCache :: WB.IdxCache t (WB.Expr t)
               -- ^ cache for normFieldAccs
              , rbExtractIntsCaches :: Map BVBound (WB.IdxCache t (WB.Expr t))
               -- ^ cache for extractInts
              , rbFnCache :: Map String (SomeSome (WB.ExprSymFn t))
              }

instance Show (ExprPath t) where
  show (ExprPath p _) =
    let
      go (Some e, bnd, msg) = "Message: " ++ msg ++ " Type: " ++ show (WI.exprType e) ++ " bounds: " ++ show bnd ++ "\n" ++ showExpr e
    in intercalate "\n--------\n" (reverse (map go p))

minBVBound :: BVBound -> BVBound -> BVBound
minBVBound (BVBound n1) (BVBound n2) = case NR.testNatCases n1 n2 of
  NR.NatCaseLT _ -> BVBound n1
  NR.NatCaseGT _ -> BVBound n2
  _ -> BVBound n1
minBVBound BVUnbounded b2 = b2
minBVBound b1 BVUnbounded = b1

data RebindException t =
    UnboundedInteger (WB.Expr t WI.BaseIntegerType)
  | RebindError String

errorHere :: HasCallStack => String -> RebindM t a
errorHere msg = do
  let (_, src): _ = getCallStack callStack
  path <- MR.asks rbPath
  nm <- MR.asks rbFunName
  let msg' = "In expression path:\n" ++ show path ++ "\n Error Message: " ++ msg ++ " at: " ++ prettySrcLoc src ++ "\n" ++ "When normalizing function: " ++ T.unpack nm
  ME.throwError $ RebindError msg'

newtype RebindM t a =
  RebindM { unRB :: ME.ExceptT (RebindException t) (MR.ReaderT (RebindEnv t) (MS.StateT (RebindState t) IO)) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MS.MonadState (RebindState t)
           , MR.MonadReader (RebindEnv t)
           , ME.MonadError (RebindException t)
           )

withSym :: (forall st fs. WB.ExprBuilder t st fs -> IO a) -> RebindM t a
withSym f = do
  env <- MR.ask
  case env of
    RebindEnv {rbBuilder = sym, .. } -> IO.liftIO $ f sym

instance MonadFail (RebindM t) where
  fail msg = errorHere $ "Fail: " ++ msg

getBounds :: RebindM t BVBound
getBounds = MS.gets rbCurrentBound

getUpperBound :: RebindM t BVBound
getUpperBound = do
  getBounds >>= \case
    BVBound n -> return $ BVBound n
    BVUnbounded -> MR.asks rbDefaultMaxBV >>= \case
      Just maxbnd -> return maxbnd
      Nothing -> return BVUnbounded

evalRebindM' :: WB.ExprBuilder t st fs -> T.Text -> Maybe BVBound -> Bool -> RebindM t a -> IO (Either (RebindException t) a)
evalRebindM' sym nm bound truncateOverflow (RebindM f) = do
  nfCache <- WB.newIdxCache
  MS.evalStateT (MR.runReaderT (ME.runExceptT f) (RebindEnv sym bound emptyExprPath nm truncateOverflow)) (RebindState Map.empty BVUnbounded nfCache Map.empty Map.empty)

evalRebindM :: WB.ExprBuilder t st fs -> T.Text -> BVBound -> RebindM t a -> IO a
evalRebindM sym nm bound f = evalRebindM' sym nm (Just bound) True f >>= \case
  Left (UnboundedInteger _) -> fail "Unexpected unbounded integer"
  Left (RebindError msg) -> fail msg
  Right a -> return a

liftIO1 :: IO.MonadIO m => (a -> IO c) -> a -> m c
liftIO1 f a = IO.liftIO $ f a

liftIO2 :: IO.MonadIO m => (a -> b -> IO c) -> a -> b -> m c
liftIO2 f a b = IO.liftIO $ f a b

-- | Turn a given bitvector expression into 'Some' bitvector expression of an unknown length.
-- Throws an exception if the given bitvector exceeds the current bounds.
mkSomeBV :: WB.Expr t (WI.BaseBVType n)
         -> RebindM t (Some (BVExpr t))
mkSomeBV expr = withExpr "mkSomeBV" expr $ withBVSize expr $ do
  curBound <- getBounds
  case compare (BVBound (bvSize expr)) curBound of
    LT -> return $ Some $ BVExpr expr
    EQ -> return $ Some $ BVExpr expr
    GT -> do
      BVBound maxn <- getBounds
      MR.asks rbTruncateOverflow >>= \case
        True -> safeTruncate expr maxn >>= mkSomeBV
        False -> fail $ "mkSomeBV: Bitvector of size:" ++ show (bvSize expr) ++ "exceeds current bounds: " ++ show curBound ++ "\n" ++ showExpr expr

-- | Similar to above, but we drop any bits (unchecked) that exceed the bound instead of erroring
truncateToBound :: WB.Expr t (WI.BaseBVType n)
                -> RebindM t (Some (BVExpr t))
truncateToBound e = do
  getBounds >>= \case
    BVBound n -> withBVSize e $ case NR.testNatCases (bvSize e) n of
      NR.NatCaseGT NR.LeqProof -> withSym $ \sym -> (Some . BVExpr) <$> WI.bvTrunc sym n e
      NR.NatCaseLT NR.LeqProof -> mkSomeBV e
      NR.NatCaseEQ -> mkSomeBV e
    BVUnbounded -> withBVSize e $ return $ Some $ BVExpr e



matchSizes :: BVExpr t n
           -> BVExpr t n'
           -> RebindM t (Pair (BVExpr t) (BVExpr t))
matchSizes (BVExpr e1) (BVExpr e2) = withSym $ \sym -> matchSizes' sym e1 e2

mkBound :: NR.NatRepr n
        -> RebindM t BVBound
mkBound n = case NR.isPosNat n of
  Just NR.LeqProof -> return $ BVBound n
  Nothing -> fail $ "mkBound: non-positive bounds given."

setBound :: BVBound
         -> RebindM t ()
setBound bnd = MS.modify $ \st -> st { rbCurrentBound = bnd }

incBound :: RebindM t ()
incBound = getBounds >>= \case
  BVUnbounded -> return ()
  BVBound maxn -> do
    pos_bnd <- return $ NR.leqProof (NR.knownNat @1) maxn
    NR.LeqProof <- return $ NR.leqAdd pos_bnd (NR.knownNat @1)
    setBound (BVBound (NR.incNat maxn))

decBound :: RebindM t ()
decBound = reduceBoundBy (NR.knownNat @1)

withBounds' :: NR.NatRepr n
           -> RebindM t a
           -> RebindM t a
withBounds' n f = do
  bnd <- mkBound n
  withBounds bnd f

withBounds :: BVBound -> RebindM t a -> RebindM t a
withBounds bnd f = do
  bnd' <- MS.gets rbCurrentBound
  setBound bnd
  a <- f
  setBound bnd'
  return a

withNoBound :: RebindM t a -> RebindM t a
withNoBound f =  withBounds BVUnbounded $ f

withBVBounds :: WB.Expr t (WI.BaseBVType n)
             -> RebindM t a
             -> RebindM t a
withBVBounds e f = withBVSize e $ withBounds' (bvSize e) f

restoreBounds :: RebindM t a -> RebindM t a
restoreBounds f = do
  bnd <- getBounds
  withBounds bnd $ f

withExpr :: Show a
         => String
         -> WB.Expr t tp
         -> RebindM t a
         -> RebindM t a
withExpr msg e f = do
  env <- MR.ask
  curBound <- getBounds
  ExprPath p s <- rbPath <$> MR.ask
  MR.local (\env -> env {rbPath = addToPath msg e curBound (rbPath env)}) $ f

updateBoundOf :: WB.ExprBoundVar t WI.BaseIntegerType -> RebindM t ()
updateBoundOf bv = do
  bvmap <- MS.gets rbBVMap
  curbound <- getBounds
  case Map.lookup bv bvmap of
    Just bound -> do
      MS.modify $ \st -> st { rbBVMap = Map.insert bv (minBVBound curbound bound) bvmap }
    Nothing -> do
      MS.modify $ \st -> st { rbBVMap = Map.insert bv curbound bvmap }

getUpperBoundOf :: WB.ExprBoundVar t WI.BaseIntegerType -> RebindM t BVBound
getUpperBoundOf bv = do
  bvmap <- MS.gets rbBVMap
  case Map.lookup bv bvmap of
    Just bnd -> return bnd
    Nothing -> MR.asks rbDefaultMaxBV >>= \case
      Just maxbnd -> return maxbnd
      Nothing -> fail $ "getUpperBoundOf: missing bound for" ++ show bv


-- | Normalize an integer expression, then extract its bitvector-equivalent.
extractBitV :: WB.Expr t WI.BaseIntegerType
            -> RebindM t (Some (BVExpr t))
extractBitV expr = extractInts' expr >>= extractBitV'

withPosNat :: (Integral a, Show a)
           => a
           -> (forall n. 1 <= n => NR.NatRepr n -> f)
           -> f
withPosNat i f
 | Just (Some nr) <- NR.someNat i
 , Just NR.LeqProof <- NR.isPosNat nr
 = f nr
withPosNat 0 f = f (NR.knownNat @1)

-- | Make a bitvector of sufficient length to represent the given integer and its sign.
-- This maintains the invariant that sbvToInteger (mkSomeLitBV i) = i for any i.
mkSomeLitSBV :: Integer -> RebindM t (Some (BVExpr t))
mkSomeLitSBV i | i > 0 = withPosNat ((integerLog2 (i*2))+1) $ \nr -> (withSym $ \sym -> WI.bvLit sym nr i) >>= mkSomeBV
mkSomeLitSBV i | i < 0 = withPosNat ((integerLog2 ((-i)*2))+1) $ \nr -> (withSym $ \sym -> WI.bvLit sym nr i) >>= mkSomeBV
mkSomeLitSBV 0 = (withSym $ \sym -> WI.bvLit sym (NR.knownNat @1) 0) >>= mkSomeBV


extractInts :: forall t tp
             . WB.Expr t tp
            -> RebindM t (WB.Expr t tp)
extractInts expr = withExprBound expr $ do
  case WB.exprMaybeId expr of
    Just idx -> do
      caches <- MS.gets rbExtractIntsCaches
      curBound <- getBounds
      case Map.lookup curBound caches of
        Just cache -> (IO.liftIO $ WB.lookupIdx cache idx) >>= \case
          Just expr' -> return expr'
          _ -> do
            expr' <- go
            WB.insertIdxValue cache idx expr'
            return expr'
        _ -> do
          cache <- IO.liftIO $ WB.newIdxCache
          MS.modify $ \st -> st { rbExtractIntsCaches = Map.insert curBound cache caches }
          expr' <- go
          WB.insertIdxValue cache idx expr'
          return expr'
    Nothing -> go
  where
    go :: RebindM t (WB.Expr t tp)
    go = do
      expr' <- extractInts' expr
      case WI.exprType expr' of
        WI.BaseIntegerRepr -> do
          Some (BVExpr expr'') <- extractBitV' expr'
          withSym $ \sym -> WI.sbvToInteger sym expr''
        _ -> return expr'


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
