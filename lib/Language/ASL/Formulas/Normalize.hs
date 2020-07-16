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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Language.ASL.Formulas.Normalize
    ( deserializeAndNormalize
    , normalizeSymFnEnv
    ) where

import           Prelude hiding ( fail )
import           GHC.Stack
import           GHC.TypeLits

import           Control.Monad ( forM, void )
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

import           Data.Kind
import qualified Data.Map.Ordered as OMap
import           Data.List ( intercalate )
import qualified Data.Text as T
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IORef as IO

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.Context as Ctx

import qualified What4.Interface as WI
import qualified What4.Symbol as WI
import qualified What4.SemiRing as WI
import qualified What4.Expr.Builder as WB
import qualified What4.Expr.WeightedSum as WSum
import           What4.Utils.Util ( SomeSome(..) )

import qualified What4.Serialize.Printer as WP

-- from this package
import qualified Language.ASL.Formulas.Serialize as FS
import           Data.Parameterized.CtxFuns
import qualified What4.Expr.ExprTree as AT
import           What4.Expr.ExprTree ( withSym, forWithIndex )

data BuilderData t = NoBuilderData


-- | Normalize and re-serialize a serialized formula library.
normalizeSymFnEnv :: FS.SExpr -> Maybe FS.SExpr -> IO (FS.SExpr, Maybe FS.SExpr)
normalizeSymFnEnv funsexpr minstexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  WB.startCaching sym
  NormalizeSymFnEnv _ funsexprsrev proxyFns <- deserializeAndNormalize sym funsexpr
  let normFunSExprs = reverse $ (funsexprsrev)

  minstexpr' <- case minstexpr of
    Just instexpr -> do
      symFnEnv <- FS.getSymFnEnv instexpr
      instrPromises <- forM symFnEnv $ \(nm, instrSexpr) -> forkResult $ do
        reserializeInstr (Map.fromList proxyFns) nm instrSexpr
      instrs <- mapM (\f -> f >>= return) instrPromises
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
                 -> IO (T.Text, FS.SExpr)
reserializeInstr env name sexpr = do
  Some r <- newIONonceGenerator
  sym <- WB.newExprBuilder WB.FloatRealRepr NoBuilderData r
  doSerialize sym
  where
    doSerialize :: forall sym t st fs
                 . sym ~ WB.ExprBuilder t st fs
                => WI.IsSymExprBuilder sym
                => sym
                -> IO (T.Text, FS.SExpr)
    doSerialize sym = do
      ref <- IO.newIORef (Map.empty :: Map T.Text (SomeSome (WI.SymFn sym)))
      let functionMaker = FS.lazyFunctionMaker sym (env, ref) (FS.uninterpFunctionMaker sym) `FS.composeMakers` FS.uninterpFunctionMaker sym
      SomeSome symFn <- FS.deserializeSymFn' functionMaker sexpr
      putStrLn $ "Reserializing Instruction: " ++ (T.unpack name)
      symFn' <- reduceSymFn sym name symFn
      return $! (name, FS.serializeSymFn symFn')


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

    -- Trivial functions shouldn't be normalized, but instead simply inlined everywhere
    -- they appear
    shouldInline :: WB.ExprSymFn t args ret -> Bool
    shouldInline symFn = case WB.symFnInfo symFn of
      WB.DefinedFnInfo _ expr _ -> exprDepthBounded 7 expr
      _ -> False
    
    augmentEnv :: T.Text
               -> SomeSome (WI.SymFn sym)
               -> NormalizeSymFnEnv sym
               -> IO (NormalizeSymFnEnv sym)
    augmentEnv nm (SomeSome symFn) (NormalizeSymFnEnv env normfns proxyfuns) = case shouldInline symFn of
      True -> do
        putStrLn $ "Inlining Function: " ++ (T.unpack nm)
        symFn' <- FS.expandSymFn sym symFn
        return $! NormalizeSymFnEnv
          { envAllFns = Map.insert nm (SomeSome symFn') env
          , envNormFns = normfns
          , envProxyFns = (nm, FS.serializeSymFn symFn') : proxyfuns
          }
      False -> do
        putStrLn $ "Normalizing Function: " ++ (T.unpack nm)
        putStrLn $ "Number of functions so far: " ++ show (length normfns)
        (symFn', innerSymFn) <- normalizeSymFn sym nm symFn
        let
          nm' = WI.solverSymbolAsText (WB.symFnName innerSymFn)
          env' = Map.insert nm' (SomeSome innerSymFn) env
        return $! NormalizeSymFnEnv
          { envAllFns = Map.insert nm (SomeSome symFn') env'
          , envNormFns = [(nm', FS.serializeSymFn innerSymFn)] ++ normfns
          , envProxyFns = (nm, FS.serializeSymFn symFn') : proxyfuns
          }

type family IntToBV (tp :: WI.BaseType) :: WI.BaseType where
  IntToBV WI.BaseIntegerType = IntegerBVType
  IntToBV tp = tp

data IntToBVWrapper :: TyFun WI.BaseType WI.BaseType -> Type
type instance Apply IntToBVWrapper t = IntToBV t

data IntToBVRepr tp tpp where
  IntToBVInt :: IntToBVRepr WI.BaseIntegerType IntegerBVType
  IntToBVElse :: WI.BaseTypeRepr tp -> IntToBVRepr tp tp

intToBVRepr :: WI.BaseTypeRepr tp -> IntToBVRepr tp (IntToBV tp)
intToBVRepr repr = case repr of
  WI.BaseIntegerRepr -> IntToBVInt
  WI.BaseStructRepr _ -> IntToBVElse repr
  WI.BaseBoolRepr -> IntToBVElse repr
  WI.BaseBVRepr _ -> IntToBVElse repr
  WI.BaseNatRepr -> IntToBVElse repr
  WI.BaseRealRepr -> IntToBVElse repr
  WI.BaseFloatRepr _ -> IntToBVElse repr
  WI.BaseStringRepr _ -> IntToBVElse repr
  WI.BaseComplexRepr -> IntToBVElse repr
  WI.BaseArrayRepr _ _ -> IntToBVElse repr

intNormOps :: AT.ExprNormOps IntToBVWrapper t (RebindM t)
intNormOps = AT.ExprNormOps normInt unNormInt normIntRepr

normInt :: WB.Expr t tp -> RebindM t (WB.Expr t (IntToBV tp))
normInt e = case intToBVRepr (WI.exprType e) of
  IntToBVInt -> extractBitV e
  IntToBVElse _ -> extractInts e


unNormInt :: WI.BaseTypeRepr tp -> WB.Expr t (IntToBV tp) -> RebindM t (WB.Expr t tp)
unNormInt repr e = case intToBVRepr repr of
  IntToBVInt -> withSym $ \sym -> WI.sbvToInteger sym e
  IntToBVElse _ -> return e

normIntRepr :: WI.BaseTypeRepr tp -> WI.BaseTypeRepr (IntToBV tp)
normIntRepr repr = case intToBVRepr repr of
  IntToBVInt -> integerBVTypeRepr
  IntToBVElse _ -> repr

reduceSymFn :: forall sym t st fs args ret
             . sym ~ WB.ExprBuilder t st fs
            => sym
            -> T.Text
            -> WB.ExprSymFn t args ret
            -> IO (WB.ExprSymFn t args ret)
reduceSymFn sym' name symFn = case WB.symFnInfo symFn of
  WB.DefinedFnInfo args expr eval -> evalRebindM sym' name $ do
    expr' <- normFieldAccs expr
    withSym $ \sym -> WI.definedFn sym (WB.symFnName symFn) args expr' eval
  _ -> fail "reduceSymFn: unexpected function kind"

-- | Normalize a symfn by expanding its body into one-dimensional struct, and then wrapping
-- this inner function in an outer function which projects out the original struct shape. This
-- outer function is unconditionally unfolded, so it won't appear the body of any normalized
-- functions.
normalizeSymFn :: forall sym t st fs args ret
                . sym ~ WB.ExprBuilder t st fs
               => sym
               -> T.Text
               -> WB.ExprSymFn t args ret
               -> IO ( WB.ExprSymFn t args ret
                     , WB.ExprSymFn t (AT.NormBaseTypeCtx IntToBVWrapper args) (AT.NormBaseType IntToBVWrapper ret))
normalizeSymFn sym' name symFn = evalRebindM sym' name (normalizeSymFn' symFn)

normalizeSymFn' :: WB.ExprSymFn t args ret
                -> RebindM t
                     ( WB.ExprSymFn t args ret
                     , WB.ExprSymFn t (AT.NormBaseTypeCtx IntToBVWrapper args) (AT.NormBaseType IntToBVWrapper ret))
normalizeSymFn' symFn = case WB.symFnInfo symFn of
  WB.DefinedFnInfo args expr_0 _eval -> withExpr "normalize" expr_0 $ do
    expr_1 <- normFieldAccs expr_0
    (expr_2, exprBoundVars, flattenBoundVars) <- AT.normExprVars intNormOps args expr_1
    (expr_3, unflattenExpr) <- AT.flatExpr intNormOps expr_2
    let innerName = ((WB.symFnName symFn) `appendToSymbol` "_inner")
    innerSymFn <- withSym $ \sym ->
      WI.definedFn sym innerName exprBoundVars expr_3 (FC.allFC WI.baseIsConcrete)
    argExprs <- withSym $ \sym -> return $ FC.fmapFC (WI.varExpr sym) args
    flatArgExprs <- flattenBoundVars $ argExprs
    outerSymFnExpr <- withSym $ \sym -> do
      inner <- WI.applySymFn sym innerSymFn flatArgExprs
      innerExpanded <- WB.evalBoundVars sym expr_3 exprBoundVars flatArgExprs
      WI.BaseStructRepr reprs <- return $ WI.exprType inner
      -- inline any results which are simply some unmodified argument
      flds <- forWithIndex reprs $ \idx _ -> do
        fldExpanded <- WI.structField sym innerExpanded idx
        case exprIsVar fldExpanded of
          True -> return fldExpanded
          False -> WI.structField sym inner idx
      WI.mkStruct sym flds
    outerSymFnBody <-  unflattenExpr outerSymFnExpr
    outerSymFn <- withSym $ \sym -> WI.definedFn sym (WB.symFnName symFn) args outerSymFnBody (\_ -> True)
    return $ (outerSymFn, innerSymFn)
  _ -> errorHere $ "Unexpected symFn kind"

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


appendToSymbol ::  WI.SolverSymbol -> String -> WI.SolverSymbol
appendToSymbol symbol str =
  let
    symbolstr = T.unpack $ WI.solverSymbolAsText symbol
  in WI.safeSymbol (symbolstr ++ str)

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

-- | normalize struct field accesses to reduce across if-then-else expressions.
-- i.e. (field 1 (ite b (W X) (Y Z))) --> (ite b W Y)
normFieldAccs :: WB.Expr t tp -> RebindM t (WB.Expr t tp)
normFieldAccs e = do
  cache <- MS.gets rbNormFieldCache
  withSym $ \sym -> normFieldAccs' sym cache e


normFieldAccs' :: forall sym st fs t tp
               . sym ~ WB.ExprBuilder t st fs
              => sym
              -> WB.IdxCache t (WB.Expr t)
              -> WB.Expr t tp
              -> IO (WB.Expr t tp)
normFieldAccs' sym cache e = do
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
        ap' <- WB.traverseApp (normFieldAccs' sym cache) ap
        let ret = if ap == ap' then return e else WB.sbMakeExpr sym ap'
        goApp ret ap'
      WB.NonceAppExpr nae ->
        case WB.nonceExprApp nae of
          WB.FnApp symFn args -> do
            args' <- FC.traverseFC (normFieldAccs' sym cache) args
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
      (WB.StructField e' idx _) -> normField' sym cache e' idx >>= \case
        Just fld -> normFieldAccs' sym cache fld
        Nothing -> ret
      _ -> ret

normField :: forall sym st fs t ctx tp
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> WB.IdxCache t (WB.Expr t)
          -> WB.Expr t (WI.BaseStructType ctx)
          -> Ctx.Index ctx tp
          -> IO (WB.Expr t tp)
normField sym cache e idx = normField' sym cache e idx >>= \case
  Just e' -> return e'
  Nothing -> WI.structField sym e idx


normField' :: forall sym st fs t ctx tp
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> WB.IdxCache t (WB.Expr t)
          -> WB.Expr t (WI.BaseStructType ctx)
          -> Ctx.Index ctx tp
          -> IO (Maybe (WB.Expr t tp))
normField' sym cache e idx = case e of
  WB.AppExpr appExpr' -> case (WB.appExprApp appExpr') of
    WB.StructField e' idx' _  -> do
      e'' <- normFieldAccs' sym cache e'
      normField' sym cache e'' idx' >>= \case
        Just fld -> normField' sym cache fld idx
        Nothing -> return Nothing

    WB.StructCtor _ flds -> Just <$> (normFieldAccs' sym cache $ flds Ctx.! idx)
    WB.BaseIte _ _ test then_ else_ -> do
      test' <- normFieldAccs' sym cache test
      then' <- normField sym cache then_ idx
      else' <- normField sym cache else_ idx
      Just <$> (WI.baseTypeIte sym test' then' else')
    _ -> return Nothing
  _ -> return Nothing


data BVExpr t n where
  BVExpr :: 1 <= n => WB.Expr t (WI.BaseBVType n) -> BVExpr t n

instance Show (BVExpr t n) where
  show (BVExpr e) = showExpr e

instance ShowF (BVExpr t) where
  showF (BVExpr e) = showExpr e

bvSize :: WB.Expr t (WI.BaseBVType n) -> NR.NatRepr n
bvSize e = case WI.exprType e of
  WI.BaseBVRepr sz -> sz


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

-- FIXME: use this once macaw supports it
_safeMatchSizeTo :: forall t n n'
                 . 1 <= n'
                => Bool
                -> NR.NatRepr n'
                -> WB.Expr t (WI.BaseBVType n)
                -> RebindM t (WB.Expr t (WI.BaseBVType n'))
_safeMatchSizeTo signed nr e = withExpr ("safeMatchSizeTo " ++ show signed ++ " " ++ show nr) e $ do
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

-- FIXME: use this once macaw supports it
_safeIntBVMul :: WB.Expr t IntegerBVType
             -> WB.Expr t IntegerBVType
             -> RebindM t (WB.Expr t IntegerBVType)
_safeIntBVMul e1 e2 = withExpr "safeIntBVMul 1" e1 $ withExpr "safeIntBVMul 2" e2 $ do
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

-- FIXME: use this once macaw supports it
_safeIntBVAdd :: WB.Expr t IntegerBVType
             -> WB.Expr t IntegerBVType
             -> RebindM t (WB.Expr t IntegerBVType)
_safeIntBVAdd e1 e2 = withExpr "safeIntBVAdd 1" e1 $ withExpr "safeIntBVAdd 2" e2 $ do
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
  SomeSymFn _ args <- asSymFn (\nm -> nm == "uf_UNDEFINED_integer") expr
  case args of
    Ctx.Empty -> return expr
    _ -> fail ""

asSBVToInteger :: WB.Expr t tp
               -> Maybe (Some (BVExpr t), tp :~: WI.BaseIntegerType)
asSBVToInteger expr = case asSymFn (\nm -> "uf_sbvToInteger_" `T.isPrefixOf` nm) expr of
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
asIntegerToSBV expr = case asIntegerToSBV' (\nm -> "uf_uu_integerToSBV_" `T.isPrefixOf` nm) expr of
  Just result -> return result
  _ -> case WB.asApp expr of
    Just (WB.IntegerToBV ie sz) -> return $ (ie, AsBVRepr sz)
    _ -> fail ""

exprIsVar :: WB.Expr t tp -> Bool
exprIsVar e = case WB.asApp e of
  Just (WB.StructField struct _ _) -> exprIsVar struct
  _ -> case e of
    WB.BoundVarExpr _ -> True
    _ -> False

intIsBound :: Ctx.Assignment (WB.Expr t) (Ctx.EmptyCtx Ctx.::> WI.BaseIntegerType)
          -> Bool
intIsBound (Ctx.Empty Ctx.:> e) = not $ exprIsVar e


type IntegerBVType = WI.BaseBVType 65

integerBVSzRepr :: NR.NatRepr 65
integerBVSzRepr = NR.knownNat

integerBVTypeRepr :: WI.BaseTypeRepr IntegerBVType
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
    WB.BoundVarExpr _ -> wrapInFn

    _ | Just (SomeSymFn _ (Ctx.Empty Ctx.:> arg)) <- asSymFn (\nm -> nm == "extractBitVinttobv") expr
      , Just (Some (BVExpr bv), _) <- asSBVToInteger arg -> do
           bv' <- extractInts bv
           unsafeMatchSizeTo True integerBVSzRepr bv'

    _ | Just (Some (BVExpr bv), _) <- asSBVToInteger expr -> do
          bv' <- extractInts bv
          unsafeMatchSizeTo True integerBVSzRepr bv'

    _ | Just _ <- asUNDEFINEDInt expr -> withSym $ \sym -> do
          fn <- WI.freshTotalUninterpFn sym (WI.safeSymbol ("uf_UNDEFINED_bitvector_" ++ show integerBVSzRepr)) Ctx.empty integerBVTypeRepr
          WI.applySymFn sym fn Ctx.empty

    _ -> case WI.asInteger expr of
      Just i -> withSym $ \sym -> WI.bvLit sym integerBVSzRepr (BV.mkBV integerBVSzRepr i)
      _ -> errorHere $ "extractBitV: unsupported expression shape: " ++ showExpr expr
  where
    wrapInFn :: RebindM t (WB.Expr t IntegerBVType)
    wrapInFn =  withSym $ \sym -> do
      freshIntBV <- WI.freshBoundVar sym WI.emptySymbol WI.BaseIntegerRepr
      fnBody <- WI.integerToBV sym (WI.varExpr sym freshIntBV) integerBVSzRepr
      fn <- WI.definedFn sym
              (WI.safeSymbol "extractBitVinttobv")
              (Ctx.empty Ctx.:> freshIntBV)
              fnBody
              intIsBound
      WI.applySymFn sym fn (Ctx.empty Ctx.:> expr)

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
          WSum.prodEvalM unsafeIntBVMul extractBitV pd >>= \case
            Just result -> return result
            Nothing -> errorHere $ "extractBitV': SemiRingProd: unexpected failure"

    go (WB.SemiRingSum sm) =
      case WSum.sumRepr sm of
        WI.SemiRingIntegerRepr -> do
          let
            mkBV coef_int expr_int = do
              coef_bv <- withSym $ \sym -> WI.bvLit sym integerBVSzRepr (BV.mkBV integerBVSzRepr coef_int)
              expr_bv <- extractBitV expr_int
              unsafeIntBVMul coef_bv expr_bv
          WSum.evalM unsafeIntBVAdd mkBV (\i -> withSym $ \sym -> WI.bvLit sym integerBVSzRepr (BV.mkBV integerBVSzRepr i)) sm
    go (WB.StructField _ _ _) = wrapInFn

    go _ = errorHere $ "extractBitV: unsupported expression shape: " ++ showExpr expr


data ExprPath t where
  ExprPath :: [(Some (WB.Expr t), String)] -> Set (Some (WB.Expr t)) -> ExprPath t

emptyExprPath :: ExprPath t
emptyExprPath = ExprPath [] Set.empty


addToPath :: String -> WB.Expr t tp -> ExprPath t -> ExprPath t
addToPath msg e (ExprPath p s) = ExprPath ((Some e, msg) : p) (Set.insert (Some e) s)

data RebindEnv t where
  RebindEnv :: { _rbBuilder :: WB.ExprBuilder t st fs
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

instance AT.HasExprBuilder t (RebindM t) where
  getExprBuilder = do
    RebindEnv sym _ _ <- MR.ask
    return $ AT.SomeExprBuilder sym

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


withExpr :: String
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
