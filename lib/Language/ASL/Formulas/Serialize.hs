{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Language.ASL.Formulas.Serialize
  ( printSExpr
  , parseSExpr
  , serializeSymFn'
  , serializeSymFn
  , mkSymFnEnvEntry
  , assembleSymFnEnv
  , serializeSymFnEnv
  , deserializeSymFn'
  , deserializeSymFn
  , deserializeSymFnEnv
  , filteredFunctionMaker
  , uninterpFunctionMaker
  , SExpr
  , NamedSymFnEnv
  ) where

import           Prelude hiding ( fail )

import           GHC.Stack ( HasCallStack, callStack, getCallStack, withFrozenCallStack, prettySrcLoc )
import           Control.Monad ( foldM, when )
import qualified Control.Monad.Except as ME
import           Control.Monad.Fail ( MonadFail, fail )
import           Control.Monad.IO.Class ( MonadIO(..) )

import qualified Data.Text as T
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.SCargot.Repr.Rich as SE

import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )

import qualified What4.Symbol as WI
import qualified What4.Interface as WI
import qualified What4.Expr.Builder as WB

import           What4.Utils.Util ( SomeSome(..) )
import qualified What4.Utils.Util as U

import qualified What4.Serialize.Printer as S ( pattern L, pattern A ) 
import           What4.Serialize.Printer ( Atom(..), SExpr )
import qualified What4.Serialize.Printer as WP
import qualified What4.Serialize.Parser as WPD

-- Mapping formal names to ExprSymFns
type ExprSymFnEnv t = Map T.Text (SomeSome (WB.ExprSymFn t))

type FnNameEnv t = OMap (WP.SomeSymFn t) T.Text

printSExpr :: SExpr -> T.Text
printSExpr sexpr = WP.printSExpr mempty sexpr

data FunSig args ret = FunSig { fsName :: T.Text
                              , fsArgs :: Ctx.Assignment WI.BaseTypeRepr args
                              , fsRet :: WI.BaseTypeRepr ret
                              }
  deriving Show

mkFunSig :: WB.ExprSymFn t args ret -> FunSig args ret
mkFunSig symFn = FunSig (WI.solverSymbolAsText $ WB.symFnName symFn) (WI.fnArgTypes symFn) (WI.fnReturnType symFn)

mkSigEnv :: FnNameEnv t -> [(T.Text, SomeSome FunSig)]
mkSigEnv env = map go (OMap.assocs env)
  where
    go :: (WP.SomeSymFn t, T.Text) -> (T.Text, SomeSome FunSig)
    go (WP.SomeSymFn symFn, nm) = (nm, SomeSome $ mkFunSig symFn)

serializeFunSig :: FunSig args ret -> SExpr
serializeFunSig (FunSig name args ret) =
  S.L [ S.A (AStr name)
      , S.L (WP.convertBaseTypes args)
      , WP.serializeBaseType ret
      ]

serializeSigEnv :: [(T.Text, SomeSome FunSig)] -> SExpr
serializeSigEnv binds = S.L (map go binds)
  where
    go :: (T.Text, SomeSome FunSig) -> SExpr
    go (nm, SomeSome funsig) = S.L [ S.A (AStr nm), serializeFunSig funsig ]

extractEnv :: FnNameEnv t -> ExprSymFnEnv t
extractEnv env = Map.fromList $ map go (OMap.assocs env)
  where
    go :: (WP.SomeSymFn t, T.Text) -> (T.Text, SomeSome (WB.ExprSymFn t))
    go (WP.SomeSymFn symFn, nm) = (nm, SomeSome symFn)

serializeSymFn' :: WB.ExprSymFn t args ret -> (SExpr, ExprSymFnEnv t)
serializeSymFn' symFn =
  let
    pcfg = WP.defaultConfig { WP.cfgAllowFreeVars = False
                            , WP.cfgAllowFreeSymFns = True
                            }
    result = WP.serializeSymFnWithConfig pcfg symFn
    env = WP.resSymFnEnv result
    sexpr = S.L [
                S.L [ S.A $ AId "SigEnv"
                    , serializeSigEnv $ mkSigEnv env
                    ]
              , S.L [ S.A $ AId "SymFn"
                    , WP.resSExpr result
                    ]
              ]
  in (sexpr, extractEnv env)

serializeSymFn :: WB.ExprSymFn t args ret -> SExpr
serializeSymFn symFn = fst $ serializeSymFn' symFn

mkSymFnEnvEntry :: T.Text -> SExpr -> SExpr
mkSymFnEnvEntry nm sexpr = S.L [ S.A (AStr nm), sexpr ]

assembleSymFnEnv :: [SExpr] -> SExpr
assembleSymFnEnv symFnEnvSExprs = S.L [ S.A (AId "SymFnEnv"), S.L symFnEnvSExprs ]

serializeSymFnEnv :: [(T.Text, SomeSome (WB.ExprSymFn t))] -> SExpr
serializeSymFnEnv symFnEnv = assembleSymFnEnv (map go symFnEnv)
  where
    go :: (T.Text, SomeSome (WB.ExprSymFn t)) -> SExpr
    go (nm, SomeSome symFn) = mkSymFnEnvEntry nm (serializeSymFn symFn)


throwErr :: HasCallStack => MonadFail m => String -> m a
throwErr msg = do
  let (_, src): _ = getCallStack callStack
  fail ("At: " ++ prettySrcLoc src ++ ": " ++ msg) 

badSExpr :: HasCallStack => MonadFail m => SExpr -> m a
badSExpr sexpr = withFrozenCallStack (throwErr $ "Unexpected s-expression: " ++ show sexpr)

parseSExpr :: MonadFail m => T.Text -> m SExpr
parseSExpr src = case WPD.parseSExpr src of
  Left err -> throwErr err
  Right sexpr -> return sexpr

deserializeBaseType :: MonadFail m => SExpr -> m (Some WI.BaseTypeRepr)
deserializeBaseType sexpr = case WPD.deserializeBaseType sexpr of
  Left err -> throwErr err
  Right bt -> return bt

deserializeBaseTypes :: MonadFail m => [SExpr] -> m (Some (Ctx.Assignment WI.BaseTypeRepr))
deserializeBaseTypes sexprs = case WPD.readBaseTypes (S.L sexprs) of
  Left err -> throwErr err
  Right bt -> return bt

deserializeFunSig :: MonadFail m => SExpr -> m (SomeSome FunSig)
deserializeFunSig sexpr = case sexpr of
  S.L [ S.A (AStr name)
      , S.L argsSexprs
      , retSexpr
      ] -> do
    Some args <- deserializeBaseTypes argsSexprs
    Some ret <- deserializeBaseType retSexpr
    return $ SomeSome $ FunSig name args ret
  _ -> badSExpr sexpr


deserializeSigEnv :: forall m. MonadFail m => SExpr -> m [(T.Text, SomeSome FunSig)]
deserializeSigEnv sexpr = case sexpr of
  S.L formals -> mapM go formals
  _ -> badSExpr sexpr
  where
    go :: SExpr -> m (T.Text, SomeSome FunSig)
    go sexpr' = case sexpr' of
      S.L [ S.A (AStr nm), funSigSexpr ] -> do
        funSig <- deserializeFunSig funSigSexpr
        return $ (nm, funSig)
      _ -> badSExpr sexpr'

-- Make a function out of a formal name and an expected signature
type FunctionMaker m sym = forall args ret. T.Text -> FunSig args ret -> m (WI.SymFn sym args ret)


deserializeSymFnBindingEnv :: forall m sym
                            . MonadFail m => sym
                           -> FunctionMaker m sym
                           -> SExpr
                           -> m (SExpr, Map T.Text (WPD.SomeSymFn sym))
deserializeSymFnBindingEnv _sym mkfun sexpr = case sexpr of
  S.L [ S.L [ S.A (WP.AId "SigEnv"), sigEnvSexpr ]
      , S.L [ S.A (WP.AId "SymFn"), symFnSexpr ]
      ] -> do
    sigEnv <- deserializeSigEnv sigEnvSexpr
    symFnEnv <- Map.fromList <$> mapM go sigEnv
    return $ (symFnSexpr, symFnEnv)
  _ -> badSExpr sexpr
  where
    go :: (T.Text, SomeSome FunSig) -> m (T.Text, WPD.SomeSymFn sym)
    go (nm, SomeSome funsig) = do
      symFn <- mkfun nm funsig
      return $ (nm, WPD.SomeSymFn symFn)

-- Mapping formal handles to functions
type SymFnEnv sym = Map T.Text (SomeSome (WI.SymFn sym))

deserializeSymFn' :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                 => MonadFail m
                 => MonadIO m
                 => sym
                 -> FunctionMaker m sym
                 -> SExpr
                 -> m (SomeSome (WI.SymFn sym))
deserializeSymFn' sym mkfun sexpr = do
  (symFnSexpr, symFnEnv) <- deserializeSymFnBindingEnv sym mkfun sexpr
  let
    mklookup nm = return $ Map.lookup nm symFnEnv
    pcfg = (WPD.defaultConfig sym){ WPD.cSymFnLookup = mklookup }
  WPD.SomeSymFn symFn <- liftIO $ do
    WPD.deserializeSymFnWithConfig pcfg symFnSexpr >>= \case
      Left err -> throwErr (err ++ "\n" ++ show symFnSexpr)
      Right result -> return result
  return $ SomeSome symFn

fnMakerFromEnv :: (MonadFail m, WI.IsSymExprBuilder sym)
               => sym
               -> SymFnEnv sym
               -> FunctionMaker m sym
fnMakerFromEnv sym env formalName sig = case Map.lookup formalName env of
  Just (SomeSome symFn) -> do
    Refl <- matchSigs sym sig symFn
    return symFn
  Nothing -> throwErr $ "Missing expected formal function in environment: " ++ T.unpack formalName

deserializeSymFn :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                 => MonadFail m
                 => MonadIO m
                 => sym
                 -> SymFnEnv sym
                 -> SExpr
                 -> m (SomeSome (WI.SymFn sym))
deserializeSymFn sym env sexpr = deserializeSymFn' sym (fnMakerFromEnv sym env) sexpr

-- Mapping informal (externally-visible) function names to functions
type NamedSymFnEnv sym = Map T.Text (SomeSome (WI.SymFn sym))

matchSigs :: (MonadFail m, WI.IsSymExprBuilder sym)
          => sym
          -> FunSig args ret
          -> WI.SymFn sym args' ret'
          -> m (args Ctx.::> ret :~: args' Ctx.::> ret')
matchSigs _sym sig symFn =
  case (testEquality (WI.fnArgTypes symFn) (fsArgs sig), testEquality (WI.fnReturnType symFn) (fsRet sig)) of
      (Just Refl, Just Refl) -> return Refl
      _ -> throwErr $
             "Mismatch in expected type for function in environment."
             ++ "\nExpected: " ++ show sig
             ++ "\nGot: " ++ show (FunSig (fsName sig) (WI.fnArgTypes symFn)  (WI.fnReturnType symFn))

lookupFnSig :: (MonadFail m, WI.IsSymExprBuilder sym)
            => sym
            -> NamedSymFnEnv sym
            -> FunSig args ret
            -> m (Maybe (WI.SymFn sym args ret))
lookupFnSig sym env sig = case Map.lookup (fsName sig) env of
  Just (SomeSome symFn) -> do
    Refl <- matchSigs sym sig symFn
    return $ Just symFn
  _ -> return Nothing

deserializeSymFnEnv :: forall sym m
                     . (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                    => MonadFail m
                    => MonadIO m
                    => sym
                    -> NamedSymFnEnv sym
                    -> FunctionMaker m sym
                    -> SExpr
                    -> m [(T.Text, SomeSome (WI.SymFn sym))]
deserializeSymFnEnv sym env mkuninterp sexpr = case sexpr of
  S.L [ S.A (AId "SymFnEnv")
      , S.L symFnSExprs ] -> do
    (_, symFns) <- foldM go (env, []) symFnSExprs
    return $ reverse $ symFns
  where
    mkFun :: NamedSymFnEnv sym -> FunctionMaker m sym
    mkFun env' formalName sig = lookupFnSig sym env' sig >>= \case
      Just symFn -> return symFn
      Nothing -> mkuninterp formalName sig

    go :: (NamedSymFnEnv sym, [(T.Text, SomeSome (WI.SymFn sym))])
       -> SExpr
       -> m (NamedSymFnEnv sym, [(T.Text, SomeSome (WI.SymFn sym))])
    go (env', symFns) = \case
      S.L [ S.A (AStr nm), symFnSExpr ] -> do
        symFn <- deserializeSymFn' sym (mkFun env') symFnSExpr
        return $ (Map.insert nm symFn env', (nm, symFn) : symFns)
      x -> badSExpr x

uninterpFunctionMaker :: forall sym m. (WI.IsSymExprBuilder sym, MonadIO m) => sym -> FunctionMaker m sym
uninterpFunctionMaker sym _formalName sig = do
  liftIO $ WI.freshTotalUninterpFn sym (U.makeSymbol (T.unpack (fsName sig))) (fsArgs sig) (fsRet sig)

filteredFunctionMaker :: (WI.IsSymExprBuilder sym, MonadFail m, MonadIO m) => sym -> (T.Text -> Bool) -> FunctionMaker m sym
filteredFunctionMaker sym f formalName sig = do
  when (not $ f $ fsName sig) $
    fail $ "Unexpected uninterpreted function: " ++ show sig
  uninterpFunctionMaker sym formalName sig
