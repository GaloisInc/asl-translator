{-# LANGUAGE GADTs #-}
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

module Language.ASL.Formulas.Normalize
    ( deserializeAndNormalize
    , normalizeSymFnEnv
    ) where

import           Control.Monad ( liftM, unless, forM, when, void )
import qualified Control.Monad.ST as ST
import           Control.Lens hiding (Index, (:>), Empty)

import qualified Control.Monad.Trans.State as MS hiding ( get, put )
import qualified Control.Monad.State as MS
import qualified Control.Monad.IO.Class as IO
import qualified Control.Concurrent.MVar as IO
import qualified Control.Concurrent as IO

import           Data.Proxy
import           Data.List ( intercalate )
import           Data.Maybe ( catMaybes, mapMaybe )
import qualified Data.Text as T
import qualified Data.HashTable.Class as H
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IORef as IO
import qualified Text.PrettyPrint.ANSI.Leijen as LPP

import           Data.Parameterized.Pair
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Context ( type (::>), pattern (:>), EmptyCtx, pattern Empty, (<++>), type (<+>) )
import qualified Data.Parameterized.Context as Ctx

-- from this package
import           Data.Parameterized.CtxFuns

import qualified What4.Interface as WI
import qualified What4.Symbol as WI
import qualified What4.Expr.Builder as WB
import           What4.Utils.Util ( SomeSome(..) )

import qualified Language.ASL.Formulas.Serialize as FS
import           Language.ASL.Types ( LabeledValue(..), projectValue, projectLabel )

import           Debug.Trace

data BuilderData t = NoBuilderData

-- | Normalize and re-serialize a serialized formula library.
normalizeSymFnEnv :: FS.SExpr -> Maybe FS.SExpr -> IO (FS.SExpr, Maybe FS.SExpr)
normalizeSymFnEnv funsexpr minstexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  putStrLn $ "Parsing and normalizing function environment..."
  NormalizeSymFnEnv env funsexprsrev proxyFns <- deserializeAndNormalize sym funsexpr
  let normFunSExprs = reverse $ (proxyFns ++ funsexprsrev)
  putStrLn $ "Finished normalization functions. Serializing."
  funsexpr' <- return $ FS.assembleSymFnEnv $ map (uncurry FS.mkSymFnEnvEntry) normFunSExprs

  minstexpr' <- case minstexpr of
    Just instexpr -> do
      putStrLn $ "Parsing and normalizing instructions.."
      symFnEnv <- FS.getSymFnEnv instexpr
      instrPromises <- forM symFnEnv $ \(nm, instrSexpr) -> forkResult $ do
        sexprs' <- reserializeInstr (Map.fromList proxyFns) nm instrSexpr
        return $! map (uncurry FS.mkSymFnEnvEntry) sexprs'
      instrs <- liftM concat $ mapM (\f -> f >>= return) instrPromises
      putStrLn $ "Finished normalizing instructions. Serializing..."
      return $ Just $ FS.assembleSymFnEnv instrs
    Nothing -> return Nothing

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
                 -> IO [(T.Text, FS.SExpr)]
reserializeInstr env name sexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  doSerialize sym
  where
    doSerialize :: forall sym t st fs
                 . sym ~ WB.ExprBuilder t st fs
                => WI.IsSymExprBuilder sym
                => sym
                -> IO [(T.Text, FS.SExpr)]
    doSerialize sym = do
      ref <- IO.newIORef (Map.empty :: Map T.Text (SomeSome (WI.SymFn sym)))
      let functionMaker = FS.lazyFunctionMaker sym (env, ref) `FS.composeMakers` FS.uninterpFunctionMaker sym
      SomeSome symFn <- FS.deserializeSymFn' functionMaker sexpr
      (symFn', normSymFns) <- normalizeSymFn sym name symFn
      return $! (mapMaybe serializeEmbedded normSymFns ++ [(name, FS.serializeSymFn symFn')])

    serializeEmbedded :: SomeSome (EmbeddedSymFn t) -> Maybe (T.Text, FS.SExpr)
    serializeEmbedded (SomeSome eSymFn)
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

    getSymFnEntry :: SomeSome (EmbeddedSymFn t) -> Maybe (T.Text, SomeSome (WI.SymFn sym))
    getSymFnEntry (SomeSome eSymFn) = case eSymFnInlined eSymFn of
      False -> Just (eSymFnName eSymFn, eSymFnSome eSymFn)
      True -> Nothing
    
    augmentEnv :: T.Text
               -> SomeSome (WI.SymFn sym)
               -> NormalizeSymFnEnv sym
               -> IO (NormalizeSymFnEnv sym)
    augmentEnv nm (SomeSome symFn) (NormalizeSymFnEnv env normfns proxyfuns) = do
      -- putStrLn $ "Normalizing: " ++ (T.unpack nm)
      -- putStrLn $ "Number of functions so far: " ++ show (length normfns)
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


-- | A wrapper for treating ASL functions and instructions uniformly
data ExprForm f tp where
  ExprFormRet :: Ctx.Assignment f glbs
              -> Ctx.Assignment f rets
              -> ExprForm f (WI.BaseStructType (EmptyCtx ::> WI.BaseStructType glbs ::> WI.BaseStructType rets))
  -- ^ Functions may have a return value, which is tupled with the set of modified globals
  ExprFormSimple :: Ctx.Assignment f ctx
                 -> ExprForm f (WI.BaseStructType ctx)
  -- ^ Instructions only return a set of modified globals

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
    go :: (Ctx.Assignment f ctx, Ctx.Assignment g ctx) -> [Pair f g] -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
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
               -> IO (WB.ExprSymFn t args ret, [SomeSome (EmbeddedSymFn t)])
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
    resultTree <- generateTree WI.exprType (WI.structField sym) expr
    eSymFnsTree <- traverseTreeWithIndex (mkSymFnAt allArgs allFreshExprs) resultTree
    eSymFnExprs <- traverseAssignmentTree (\eSymFn -> return $ eSymFnExpr eSymFn) eSymFnsTree

    -- reconstruct an expression equivalent to the original with the computed functions
    -- ==> ((f_1_1 (S'[2:2]), f_1_2 S'[2:1]), f_2 (S'[1], S'[2:2]))
    expr' <- collapseAssignmentTree return (WI.mkStruct sym) eSymFnExprs
    
    symFn' <- WI.definedFn sym (WB.symFnName symFn) outerArgVars expr' (\_ -> True)
    eSymFnList <- return $ map (\(Some eSymFn) -> SomeSome eSymFn) $ flattenTree eSymFnsTree
    return $! (symFn', eSymFnList)
    where
      mkSymFnAt :: forall allargs tp
                 . Ctx.Assignment (WB.ExprBoundVar t) allargs
                -> Ctx.Assignment (WB.Expr t) allargs
                -> [Integer]
                -> WB.Expr t tp
                -> IO (EmbeddedSymFn t allargs tp)
      mkSymFnAt allArgs allFreshExprs idxpath e =
        let
          pathstr = "_" ++ pathToString idxpath
          symbol = appendToSymbol (WB.symFnName symFn) pathstr
          name' = name <> T.pack pathstr
        in mkSymFn sym allArgs allFreshExprs symbol name' e

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
        -> Ctx.Assignment (WB.Expr t) allargs
        -- ^ fresh variants of the above bound variables, representing the arguments to the normalized function
        -> WI.SolverSymbol
        -> T.Text
        -> WB.Expr t tp
        -- ^ the expression representing the final result of a single struct member
        -> IO (EmbeddedSymFn t allargs tp)
mkSymFn sym allbvs outerExprs symbol name inexpr = do
  expr <- normExpr sym inexpr
  usedbvsSet <- liftM (Set.unions . map snd) $ ST.stToIO $ H.toList =<< WB.boundVars expr
  SubAssignment embedding subbvs <- case mkSubAssigment usedbvsSet allbvs of
    Just subbvs -> return subbvs
    Nothing -> fail $ "Invalid expression: used bound variables not a subset of arguments:" ++ showExpr expr
     ++ "\n Used:" ++ (show (map (\(Some bv) -> showExpr (WI.varExpr sym bv)) (Set.toList usedbvsSet)))
     ++ "\n All:" ++ (show (FC.toListFC (\bv -> showExpr (WI.varExpr sym bv)) allbvs))
  trivial <- alwaysInline expr subbvs
  symFn <- WI.definedFn sym symbol subbvs expr (shouldInline trivial)
  let outerExprsSub = applyEmbeddingAsn (Ctx.size subbvs) embedding outerExprs
  expr <- WI.applySymFn sym symFn outerExprsSub
  return $ EmbeddedSymFn name embedding symFn expr trivial
  where
    alwaysInline :: forall args
                  . WB.Expr t tp
                 -> Ctx.Assignment (WB.ExprBoundVar t) args
                 -> IO Bool
    alwaysInline expr bvs = case Ctx.viewAssign bvs of
      Ctx.AssignEmpty -> return True
      Ctx.AssignExtend Ctx.Empty bv | Just Refl <- testEquality (WI.varExpr sym bv) expr
        -> return $ (WI.varExpr sym bv) == expr
      _ -> return False
    
    shouldInline :: forall args
                  . Bool
                 -> Ctx.Assignment (WB.Expr t) args
                 -> Bool
    shouldInline isTrivial args = isTrivial || FC.allFC WI.baseIsConcrete args

showExpr :: WB.Expr t ret -> String
showExpr e = (LPP.displayS (LPP.renderPretty 0.4 80 (WI.printSymExpr e)) "")

trivialExpression :: sym ~ WB.ExprBuilder t st fs
                  => sym
                  -> WB.ExprBoundVar t tp
                  -> WB.Expr t tp
                  -> IO Bool
trivialExpression sym bv expr = do
  c <- WI.freshConstant sym (WI.safeSymbol "c") (WI.exprType expr)
  expr' <- WB.evalBoundVars sym expr (Ctx.singleton bv) (Ctx.singleton c)
  return $ expr == c


-- | FIXME: Unclear if this ever does anything.
reduceExpr :: forall sym st fs t args tp
            . sym ~ WB.ExprBuilder t st fs
           => sym
           -> Ctx.Assignment (WB.ExprBoundVar t) args
           -> WB.Expr t tp
           -> IO (WB.Expr t tp)
reduceExpr sym bvs e = do
  freshBvs <- FC.traverseFC (refreshBoundVar sym) bvs
  WB.evalBoundVars sym e bvs (FC.fmapFC (WI.varExpr sym) freshBvs)
  e' <- WB.evalBoundVars sym e freshBvs (FC.fmapFC (WI.varExpr sym) bvs)
  if (e == e') then
    return e
  else error $ "reduceExpr: expression changed: " ++ showExpr e ++ "\n vs.\n" ++ showExpr e'

-- | Normalize struct field accesses to reduce across if-then-else expressions.
-- i.e. (field 1 (ite b (W X) (Y Z))) --> (ite b W Y)
normExpr :: forall sym st fs t tp
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> WB.Expr t tp
          -> IO (WB.Expr t tp)
normExpr sym e = case e of
  WB.AppExpr appExpr -> do
    go $ WB.appExprApp appExpr

  _ -> return e
  where
    go :: WB.App (WB.Expr t) tp -> IO (WB.Expr t tp)
    go (WB.BaseIte _ _ test then_ else_) = do
      test' <- normExpr sym test
      then' <- normExpr sym then_
      else' <- normExpr sym else_
      WI.baseTypeIte sym test' then' else'

    go (WB.StructField e' idx _) = do
      e'' <- normExpr sym e'
      normField e'' idx
    go _ = return e

    normField :: forall ctx
               . WB.Expr t (WI.BaseStructType ctx)
              -> Ctx.Index ctx tp
              -> IO (WB.Expr t tp)
    normField e idx = case e of
      WB.AppExpr appExpr' -> case (WB.appExprApp appExpr') of
        WB.StructCtor _ flds -> do
          return $ flds Ctx.! idx
        WB.BaseIte _ _ test then_ else_ -> do
          test' <- normExpr sym test
          then' <- normField then_ idx
          else' <- normField else_ idx
          WI.baseTypeIte sym test' then' else'
        _ -> fail $ "Failed to fully normalize struct access: \n" ++ showExpr e
      _ -> fail $ "Failed to fully normalize struct access: \n" ++ showExpr e

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
