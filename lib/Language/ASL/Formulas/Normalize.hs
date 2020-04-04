{-|
Module           : Language.ASL.Translation
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Normalization of the translated ASL semantics to remove
structs and integers.


-}

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
import           GHC.TypeLits

import           Control.Monad ( liftM, forM, void )
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

import qualified Data.Map.Ordered as OMap
import           Data.List ( intercalate )
import           Data.Maybe ( catMaybes, mapMaybe )
import qualified Data.Text as T
import qualified Data.HashTable.Class as H
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IORef as IO

import           Data.Parameterized.Pair
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Context ( pattern (:>) )
import qualified Data.Parameterized.Context as Ctx

-- from this package
import           Data.Parameterized.CtxFuns

import qualified What4.Interface as WI
import qualified What4.Symbol as WI
import qualified What4.SemiRing as WI
import qualified What4.Expr.Builder as WB
import qualified What4.Expr.WeightedSum as WSum
import           What4.Utils.Util ( SomeSome(..) )

import qualified What4.Serialize.Printer as WP

import qualified Language.ASL.Formulas.Serialize as FS

data BuilderData t = NoBuilderData

-- | Normalize and re-serialize a serialized formula library.
normalizeSymFnEnv :: FS.SExpr -> Maybe FS.SExpr -> IO (FS.SExpr, Maybe FS.SExpr)
normalizeSymFnEnv funsexpr minstexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  -- WB.startCaching sym
  NormalizeSymFnEnv _ funsexprsrev proxyFns <- deserializeAndNormalize sym funsexpr
  let normFunSExprs = reverse $ (funsexprsrev)

  minstexpr' <- case minstexpr of
    Just instexpr -> do
      symFnEnv <- FS.getSymFnEnv instexpr
      instrPromises <- forM symFnEnv $ \(nm, instrSexpr) -> forkResult $ do
        reserializeInstr (Map.fromList proxyFns) nm instrSexpr
      instrs <- liftM concat $ mapM (\f -> f >>= return) instrPromises
      return $ Just $ FS.assembleSymFnEnv $ map (uncurry FS.mkSymFnEnvEntry) instrs
    Nothing -> return Nothing
  funsexpr' <- return $ FS.assembleSymFnEnv $ map (uncurry FS.mkSymFnEnvEntry) normFunSExprs

  return $ (funsexpr', minstexpr')

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
      let functionMaker = FS.lazyFunctionMaker sym (env, ref) (FS.uninterpFunctionMaker sym) `FS.composeMakers` FS.uninterpFunctionMaker sym
      SomeSome symFn <- FS.deserializeSymFn' functionMaker sexpr
      putStrLn $ "Normalizing Instruction: " ++ (T.unpack name)
      (symFn', eSymFns) <- normalizeSymFn sym name symFn True

      return $! mapMaybe serializeEmbedded eSymFns ++ [(name, FS.serializeSymFn symFn')]

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
      (symFn', normSymFns) <- normalizeSymFn sym nm symFn False
      let
        newnormfns = catMaybes $ map getSymFnEntry normSymFns
        newnormfnsSer = map (\(nm', SomeSome fn) -> (nm', FS.serializeSymFn fn)) newnormfns
        env' = foldr (\(nm',fn) env'' -> Map.insert nm' fn env'') env newnormfns
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
    go path tree' =  case tree' of
      AssignmentTreeLeaf a -> AssignmentTreeLeaf <$> f (reverse path) a
      AssignmentTreeNode nodes -> do
        nodes' <- Ctx.traverseWithIndex (\idx tree'' -> go ((fromIntegral $ Ctx.indexVal idx) : path) tree'') nodes
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
  _ -> error $ "flattenZipTreePair: unxpected tree pair"

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
    freshStruct <- collapseAssignmentTree (\bv' -> return $ WI.varExpr sym bv') (WI.mkStruct sym) freshBVTree
    return $ PairF freshStruct freshBVTree
  _ -> return $ PairF (WI.varExpr sym bv) (AssignmentTreeLeaf bv)
  where
    mkSubBVar :: forall ctx tp'
               . WB.ExprBoundVar t (WI.BaseStructType ctx)
              -> Ctx.Index ctx tp'
              -> IO (WB.ExprBoundVar t tp')
    mkSubBVar bv' idx = do
      let
        WI.BaseStructRepr reprs = WB.bvarType bv'
        repr = reprs Ctx.! idx
      WI.freshBoundVar sym ((WB.bvarName bv') `appendToSymbol` ("_" ++ show (Ctx.indexVal idx))) repr

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
               -> Bool
               -> IO (WB.ExprSymFn t args ret, [Some (EmbeddedSymFn t)])
normalizeSymFn sym name symFn topLevel
  | WB.DefinedFnInfo args initexpr _eval <- WB.symFnInfo symFn = do
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

    eSymFnsTree <- evalRebindM sym name $ do
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
        expr' <- withSym $ \sym' -> normFieldAccs sym' nfCache expr
        case exprDepthBounded 7 expr' && not topLevel of
          True -> return (expr', True)
          False -> do
            expr'' <- extractInts expr'
            return (expr'', False)

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
normalizeSymFn _ _ _ _ = error $ "normalizeSymFn: unexpected symFn kind."

-- | True if the expression is not any deeper than the given depth
exprDepthBounded :: Integer
                 -> WB.Expr t tp
                 -> Bool
exprDepthBounded 0 _ = False
exprDepthBounded i expr = case expr of
  WB.AppExpr appExpr -> FC.allFC (exprDepthBounded (i-1)) $ WB.appExprApp appExpr
  WB.NonceAppExpr nae
    | WB.FnApp _symFn args <- WB.nonceExprApp nae ->
      FC.allFC (exprDepthBounded (i-1)) $ args
  _ -> True

pathToString :: [Integer] -> String
pathToString idxpath = intercalate "_" $ map show idxpath

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
          expr2 <- extractBitV expr
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
      _ -> return $ inline

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
    revFnEnv = Map.fromList $ map (\(WP.SomeExprSymFn symFn, nm) -> (nm, WI.solverSymbolAsText $ WB.symFnName symFn)) (OMap.toAscList (WP.resSymFnEnv res))

    go a = case a of
      WP.AId nm -> case Map.lookup nm revVarEnv  of
        Just nm' -> WP.AId nm'
        _ -> case Map.lookup nm revFnEnv of
          Just nm' -> WP.AId nm'
          _ -> a
      _ -> a

  in T.unpack $ FS.printSExpr $ fmap go (WP.resSExpr res)

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
        argExpr' <- withSym $ \sym -> WI.integerToBV sym argExpr n
        return $ Const $ Some $ PairF bv argExpr'
      WrapIntSimple bv _ -> return $ Const $ Some $ PairF bv argExpr

    refreshIntVar :: forall tp'. WB.ExprBoundVar t tp'
                  -> RebindM t (WrapInt (WB.ExprBoundVar t) (WB.Expr t) tp')
    refreshIntVar bv = case WB.bvarType bv of
      WI.BaseIntegerRepr -> do
        bv_var <- withSym $ \sym -> WI.freshBoundVar sym (appendToSymbol (WB.bvarName bv) "_asBVar") integerBVTypeRepr
        expr' <- withSym $ \sym -> WI.sbvToInteger sym (WI.varExpr sym bv_var)
        return $ WrapIntInt bv_var expr'
      _ -> withSym $ \sym -> return $ WrapIntSimple bv (WI.varExpr sym bv)


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

-- | Wrap a bitvector with a runtime assertion of its validity
runtimeAssert :: WB.Expr t WI.BaseBoolType
              -> WB.Expr t (WI.BaseBVType n)
              -> RebindM t (WB.Expr t (WI.BaseBVType n))
runtimeAssert pred' e = case WI.asConstantPred pred' of
  Just True -> return e
  Just False -> fail $ "runtimeAssert: asserted False for: " ++ showExpr e
  Nothing -> do
    WI.BaseBVRepr n <- return $ WI.exprType e
    let nm = "assertBV_" ++ show (NR.intValue n)
    symFn <- mkUF nm (Ctx.empty Ctx.:> WI.BaseBoolRepr Ctx.:> WI.exprType e) (WI.exprType e)
    withSym $ \sym -> WI.applySymFn sym symFn (Ctx.empty Ctx.:> pred' Ctx.:> e)


unsafeMatchSizeTo :: forall t n n'
                 . 1 <= n'
                => Bool
                -> NR.NatRepr n'
                -> WB.Expr t (WI.BaseBVType n)
                -> RebindM t (WB.Expr t (WI.BaseBVType n'))
unsafeMatchSizeTo signed nr e = withExpr ("unsafeMatchSizeTo " ++ show signed ++ " " ++ show nr) e $ do
  WI.BaseBVRepr n <- return $ WI.exprType e
  case NR.testNatCases n nr of
    NR.NatCaseLT NR.LeqProof -> withSym $ \sym -> do
      if signed then WI.bvSext sym nr e else WI.bvZext sym nr e
    NR.NatCaseGT NR.LeqProof -> withSym $ \sym -> WI.bvTrunc sym nr e
    NR.NatCaseEQ -> return e

safeMatchSizeTo :: forall t n n'
                 . 1 <= n'
                => Bool
                -> NR.NatRepr n'
                -> WB.Expr t (WI.BaseBVType n)
                -> RebindM t (WB.Expr t (WI.BaseBVType n'))
safeMatchSizeTo signed nr e = withExpr ("safeMatchSizeTo " ++ show signed ++ " " ++ show nr) e $ do
  WI.BaseBVRepr n <- return $ WI.exprType e
  case NR.testNatCases n nr of
    NR.NatCaseLT NR.LeqProof -> withSym $ \sym -> do
      if signed then WI.bvSext sym nr e else WI.bvZext sym nr e
    NR.NatCaseGT NR.LeqProof -> do
      truncBv <- withSym $ \sym -> WI.bvTrunc sym nr e
      extBv <- withSym $ \sym -> WI.bvZext sym n truncBv
      isValid <- withSym $ \sym -> WI.isEq sym e extBv
      runtimeAssert isValid truncBv
    NR.NatCaseEQ -> return e

unsafeIntBVMul :: WB.Expr t IntegerBVType
               -> WB.Expr t IntegerBVType
               -> RebindM t (WB.Expr t IntegerBVType)
unsafeIntBVMul e1 e2 = withExpr "unsafeIntBVMul 1" e1 $ withExpr "unsafeIntBVMul 2" e2 $ do
  withSym $ \sym -> WI.bvMul sym e1 e2

safeIntBVMul :: WB.Expr t IntegerBVType
             -> WB.Expr t IntegerBVType
             -> RebindM t (WB.Expr t IntegerBVType)
safeIntBVMul e1 e2 = withExpr "safeIntBVMul 1" e1 $ withExpr "safeIntBVMul 2" e2 $ do
  (isValid, result) <- withSym $ \sym -> do
    (isOverflow, result) <- WI.mulSignedOF sym e1 e2
    isValid <- WI.notPred sym isOverflow
    return $ (isValid, result)
  runtimeAssert isValid result

unsafeIntBVAdd :: WB.Expr t IntegerBVType
               -> WB.Expr t IntegerBVType
               -> RebindM t (WB.Expr t IntegerBVType)
unsafeIntBVAdd e1 e2 = withExpr "unsafeIntBVAdd 1" e1 $ withExpr "unsafeIntBVAdd 2" e2 $ do
  withSym $ \sym -> WI.bvAdd sym e1 e2

safeIntBVAdd :: WB.Expr t IntegerBVType
             -> WB.Expr t IntegerBVType
             -> RebindM t (WB.Expr t IntegerBVType)
safeIntBVAdd e1 e2 = withExpr "safeIntBVAdd 1" e1 $ withExpr "safeIntBVAdd 2" e2 $ do
  (isValid, result) <- withSym $ \sym -> do
    (isOverflow, result) <- WI.addSignedOF sym e1 e2
    isValid <- WI.notPred sym isOverflow
    return $ (isValid, result)
  runtimeAssert isValid result

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
          bv1' <- extractBitV int1
          bv2' <- extractBitV int2
          result <- bvOp bv1' bv2'
          withSym $ \sym -> WI.sbvToInteger sym result

    _ | Just (SomeSymFn _ (Ctx.Empty Ctx.:> _arg)) <- asSymFn (\nm -> nm == "extractBitVinttobv") expr
        -> return expr

    _ | Just (expr', AsBVRepr sz) <- asIntegerToSBV expr -> do
          bv <- extractBitV expr'
          unsafeMatchSizeTo True sz bv

    WB.AppExpr appExpr -> do
      let ap = WB.appExprApp appExpr
      ap' <- WB.traverseApp extractInts ap
      let ret = if ap == ap' then return expr else withSym $ \sym -> WB.sbMakeExpr sym ap'
      goApp ret ap'

    WB.NonceAppExpr nae | WB.FnApp symFn args <- WB.nonceExprApp nae -> do
      args' <- FC.traverseFC (extractInts) args
      if (args == args') then
        return expr
      else
        withSym $ \sym -> WI.applySymFn sym symFn args'
    _ -> return expr

  where
    goApp :: RebindM t (WB.Expr t tp) -> WB.App (WB.Expr t) tp -> RebindM t (WB.Expr t tp)
    goApp ret ap = case ap of
      WB.BaseEq WI.BaseIntegerRepr a1 b1 -> do
          a2 <- extractBitV a1
          b2 <- extractBitV b1
          withSym $ \sym -> WI.isEq sym a2 b2
      WB.SemiRingLe WI.OrderedSemiRingIntegerRepr a1 b1 -> do
          a2 <- extractBitV a1
          b2 <- extractBitV b1
          eqPred <- withSym $ \sym -> WI.isEq sym a2 b2
          ltPred <- withSym $ \sym -> WI.bvSlt sym a2 b2
          withSym $ \sym -> WI.orPred sym eqPred ltPred
      _ -> ret

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
    | WI.BaseBVRepr _ <- WI.exprType arg
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
    , WI.BaseBVRepr _ <- WI.exprType expr -> return $ (arg, AsBVRepr (bvSize expr))
  _ -> fail ""

asIntegerToSBV :: WB.Expr t tp
               -> Maybe (WB.Expr t WI.BaseIntegerType, AsBVRepr tp)
asIntegerToSBV expr = case asIntegerToSBV' (\nm -> "uu_integerToSBV_" `T.isPrefixOf` nm) expr of
  Just result -> return result
  _ -> case WB.asApp expr of
    Just (WB.IntegerToBV ie sz) -> return $ (ie, AsBVRepr sz)
    _ -> fail ""

exprIsVar :: WB.Expr t tp -> Bool
exprIsVar e = case e of
  WB.BoundVarExpr _ -> True
  _ -> False

intIsBound :: Ctx.Assignment (WB.Expr t) (Ctx.EmptyCtx Ctx.::> WI.BaseIntegerType)
          -> Bool
intIsBound (Ctx.Empty Ctx.:> e) = not $ exprIsVar e

type IntegerBVType = WI.BaseBVType 65

integerBVSzRepr :: NR.NatRepr 65
integerBVSzRepr = NR.knownNat

integerBVTypeRepr :: WI.BaseTypeRepr (WI.BaseBVType 65)
integerBVTypeRepr = knownRepr

-- | Extract a bitvector from an integer expression, assuming it is already
-- in normal form.
extractBitV' :: forall t
              . WB.Expr t WI.BaseIntegerType
             -> RebindM t (WB.Expr t IntegerBVType)
extractBitV' expr = withExpr "extractBitV'" expr $ do
  case expr of
    WB.AppExpr appExpr -> do
      expr' <- go $! WB.appExprApp appExpr
      return $! expr'
    WB.BoundVarExpr _ -> withSym $ \sym -> do
      freshIntBV <- WI.freshBoundVar sym WI.emptySymbol WI.BaseIntegerRepr
      fnBody <- WI.integerToBV sym (WI.varExpr sym freshIntBV) integerBVSzRepr
      fn <- WI.definedFn sym
              (WI.safeSymbol "extractBitVinttobv")
              (Ctx.empty Ctx.:> freshIntBV)
              fnBody
              intIsBound
      WI.applySymFn sym fn (Ctx.empty Ctx.:> expr)

    _ | Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg)) <- asSymFn (\nm -> nm == "extractBitVinttobv") expr
      , Just (Some (BVExpr bv), _) <- asSBVToInteger arg -> do
           bv' <- extractInts bv
           unsafeMatchSizeTo True integerBVSzRepr bv'

    _ | Just (Some (BVExpr bv), _) <- asSBVToInteger expr -> do
          bv' <- extractInts bv
          unsafeMatchSizeTo True integerBVSzRepr bv'

    _ | Just _ <- asUNDEFINEDInt expr -> withSym $ \sym -> do
          fn <- WI.freshTotalUninterpFn sym (WI.safeSymbol ("UNDEFINED_bitvector_" ++ show integerBVSzRepr)) Ctx.empty integerBVTypeRepr
          WI.applySymFn sym fn Ctx.empty

    _ -> case WI.asInteger expr of
      Just i -> withSym $ \sym -> WI.bvLit sym integerBVSzRepr i
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
              -> RebindM t (WB.Expr t IntegerBVType)
    liftBinop a1 b1 f = do
      a2 <- extractBitV a1
      b2 <- extractBitV b1
      withSym $ \sym -> f sym a2 b2

    go :: WB.App (WB.Expr t) WI.BaseIntegerType -> RebindM t (WB.Expr t IntegerBVType)

    go (WB.BVToInteger bv) = unsafeMatchSizeTo False integerBVSzRepr bv
    go (WB.SBVToInteger bv) = unsafeMatchSizeTo True integerBVSzRepr bv
    go (WB.BaseIte _ _ test then_ else_) = liftBinop then_ else_ (\sym -> WI.baseTypeIte sym test)
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

    go (WB.SemiRingProd pd) =
      case WSum.prodRepr pd of
        WI.SemiRingIntegerRepr -> do
          Just result <- WSum.prodEvalM unsafeIntBVMul extractBitV pd
          return result

    go (WB.SemiRingSum sm) =
      case WSum.sumRepr sm of
        WI.SemiRingIntegerRepr -> do
          let
            mkBV coef_int expr_int = do
              coef_bv <- withSym $ \sym -> WI.bvLit sym integerBVSzRepr coef_int
              expr_bv <- extractBitV expr_int
              unsafeIntBVMul coef_bv expr_bv
          WSum.evalM unsafeIntBVAdd mkBV (\i -> withSym $ \sym -> WI.bvLit sym integerBVSzRepr i) sm

    go _ = fail $ "extractBitV: unsupported expression shape: " ++ showExpr expr


data ExprPath t where
  ExprPath :: [(Some (WB.Expr t), String)] -> Set (Some (WB.Expr t)) -> ExprPath t

emptyExprPath :: ExprPath t
emptyExprPath = ExprPath [] Set.empty

addToPath :: String -> WB.Expr t tp -> ExprPath t -> ExprPath t
addToPath msg e (ExprPath p s) = ExprPath ((Some e, msg) : p) (Set.insert (Some e) s)

data RebindEnv t where
  RebindEnv :: { rbBuilder :: WB.ExprBuilder t st fs
               -- ^ underlying expression builder for constructing new terms,
               -- access via 'withSym'
               , rbPath :: ExprPath t
               -- ^ the current traversal path of the normalization
               -- Used for providing context to error messages
               , rbFunName :: T.Text
               -- ^ name of the top-level function being normalized
               } -> RebindEnv t

data RebindState t =
  RebindState { rbNormFieldCache :: WB.IdxCache t (WB.Expr t)
               -- ^ cache for normFieldAccs
              , rbExtractIntsCache :: WB.IdxCache t (WB.Expr t)
               -- ^ cache for extractInts
              , rbFnCache :: Map String (SomeSome (WB.ExprSymFn t))
              }

instance Show (ExprPath t) where
  show (ExprPath p _) =
    let
      go (Some e, msg) = "Message: " ++ msg ++ " Type: " ++ show (WI.exprType e) ++ "\n" ++ showExpr e
    in intercalate "\n--------\n" (reverse (map go p))


data RebindException t = RebindError String

errorHere :: HasCallStack => String -> RebindM t a
errorHere msg = do
  let (_, src): _ = getCallStack callStack
  path <- MR.asks rbPath
  nm <- MR.asks rbFunName
  let msg' = "In expression path:\n" ++ show path ++ "\n Error Message: " ++ msg ++ " at: " ++ prettySrcLoc src ++ "\n" ++ "When normalizing function: " ++ T.unpack nm
  ME.throwError $ RebindError msg'

newtype RebindM t a =
  RebindM { _unRB :: ME.ExceptT (RebindException t) (MR.ReaderT (RebindEnv t) (MS.StateT (RebindState t) IO)) a }
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


evalRebindM' :: WB.ExprBuilder t st fs -> T.Text -> RebindM t a -> IO (Either (RebindException t) a)
evalRebindM' sym nm (RebindM f) = do
  nfCache <- WB.newIdxCache
  eiCache <- WB.newIdxCache
  MS.evalStateT (MR.runReaderT (ME.runExceptT f) (RebindEnv sym emptyExprPath nm)) (RebindState nfCache eiCache Map.empty)

evalRebindM :: WB.ExprBuilder t st fs -> T.Text -> RebindM t a -> IO a
evalRebindM sym nm f = evalRebindM' sym nm f >>= \case
  Left (RebindError msg) -> fail msg
  Right a -> return a


liftIO2 :: IO.MonadIO m => (a -> b -> IO c) -> a -> b -> m c
liftIO2 f a b = IO.liftIO $ f a b

withExpr :: Show a
         => String
         -> WB.Expr t tp
         -> RebindM t a
         -> RebindM t a
withExpr msg e f = MR.local (\env -> env {rbPath = addToPath msg e (rbPath env)}) $ f

-- | Normalize an integer expression, then extract its bitvector-equivalent.
extractBitV :: WB.Expr t WI.BaseIntegerType
            -> RebindM t (WB.Expr t IntegerBVType)
extractBitV expr = extractInts' expr >>= extractBitV'


extractInts :: forall t tp
             . WB.Expr t tp
            -> RebindM t (WB.Expr t tp)
extractInts expr = do
  case WB.exprMaybeId expr of
    Just idx -> do
      eiCache <- MS.gets rbExtractIntsCache
      (IO.liftIO $ WB.lookupIdx eiCache idx) >>= \case
        Just expr' -> return expr'
        _ -> do
          expr' <- go
          WB.insertIdxValue eiCache idx expr'
          return expr'
    Nothing -> go
  where
    go :: RebindM t (WB.Expr t tp)
    go = do
      expr' <- extractInts' expr
      case WI.exprType expr' of
        WI.BaseIntegerRepr -> do
          expr'' <- extractBitV' expr'
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
