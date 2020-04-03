{-|
Module           : Language.ASL.Formulas.Serialize
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module extends the printer and parser provided by
"What4.Serialize.Printer" and "What4.Serialize.Parser".
In particular it provides an interface for serializing
and deserializing function environments (named collections
of functions which may refer to each other).

-}

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
  , deserializeSymFnEnv'
  , deserializeSymFnEnv
  , getSymFnEnv
  , FunSig(..)
  , FunctionMaker(..)
  , mapFunctionMaker
  , envFunctionMaker
  , iteFunctionMaker
  , uninterpFunctionMaker
  , noFunctionMaker
  , lazyFunctionMaker
  , composeMakers
  , expandSymFn
  , SExpr
  , NamedSymFnEnv
  ) where

import           Prelude hiding ( fail )

import           GHC.Stack ( HasCallStack, callStack, getCallStack, withFrozenCallStack, prettySrcLoc )
import           Control.Monad ( foldM )
import           Control.Monad.Fail ( MonadFail, fail )
import           Control.Monad.IO.Class ( MonadIO(..) )

import qualified Data.Text as T
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IORef as IO

import           Data.Parameterized.Classes
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

-- | Environment mapping formal names to ExprSymFns
type ExprSymFnEnv t = Map T.Text (SomeSome (WB.ExprSymFn t))

type FnNameEnv t = OMap (WP.SomeSymFn t) T.Text

-- | Convert an s-expression into its textual representation.
printSExpr :: SExpr -> T.Text
printSExpr sexpr = WP.printSExpr mempty sexpr

-- | The signature and friendly name of a What4 function
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

-- | Serialize a What4 function as an s-expression, and return its
-- binding environment mapping formal names (appearing in the
-- resulting s-expression) to any functions which were called in
-- its body.
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

-- | Serialize a What4 function as an s-expression.
serializeSymFn :: WB.ExprSymFn t args ret -> SExpr
serializeSymFn symFn = fst $ serializeSymFn' symFn

-- | Pair a serialized function with its name to create a valid
-- function environment entry.
mkSymFnEnvEntry :: T.Text -> SExpr -> SExpr
mkSymFnEnvEntry nm sexpr = S.L [ S.A (AStr nm), sexpr ]


-- | Assemble a collection of function environment entries
-- (as created by 'mkSymFnEnvEntry') into a single function
-- environment s-expression.
assembleSymFnEnv :: [SExpr] -> SExpr
assembleSymFnEnv symFnEnvSExprs = S.L [ S.A (AId "SymFnEnv"), S.L symFnEnvSExprs ]

-- | Serialize a collection of functions into a function environment.
-- In order to be read back in by 'deserializeSymFnEnv' the functions
-- must already be topologically sorted with respect to their call graph
-- (e.g. the last function may contain calls to any other function).
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

-- | Parse text into a wellformed s-expression, failing on any parse errors.
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

-- | A 'FunctionMaker' is a recipe for constructing a What4 function from
-- a given (formal) name and expected signature. The result is either
-- an error message or a function of the expected signature.
data FunctionMaker sym where
  FunctionMaker :: sym ->
    (forall args ret m
     . (MonadIO m, MonadFail m)
    => T.Text -> FunSig args ret
    -> m (Either String (WI.SymFn sym args ret)))
    -> FunctionMaker sym

makeFunction :: MonadFail m => MonadIO m => FunctionMaker sym -> T.Text -> FunSig args ret -> m (WI.SymFn sym args ret)
makeFunction (FunctionMaker _sym f) nm sig = f nm sig >>= \case
  Left err -> fail err
  Right result -> return result

symFromMaker :: FunctionMaker sym -> sym
symFromMaker (FunctionMaker sym _) = sym

deserializeSymFnBindingEnv :: forall m sym
                            . MonadFail m
                           => MonadIO m
                           => FunctionMaker sym
                           -> SExpr
                           -> m (SExpr, Map T.Text (WPD.SomeSymFn sym))
deserializeSymFnBindingEnv fnmaker sexpr = case sexpr of
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
      symFn <- makeFunction fnmaker nm funsig
      return $ (nm, WPD.SomeSymFn symFn)

-- | Environment mapping formal names to functions
type SymFnEnv sym = Map T.Text (SomeSome (WI.SymFn sym))

-- | Deserialize a single What4 function, translating function calls
-- according to the provided 'FunctionMaker'.
deserializeSymFn' :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                 => MonadFail m
                 => MonadIO m
                 => FunctionMaker sym
                 -> SExpr
                 -> m (SomeSome (WI.SymFn sym))
deserializeSymFn' fnmaker sexpr = do
  (symFnSexpr, symFnEnv) <- deserializeSymFnBindingEnv fnmaker sexpr
  let
    mklookup nm = return $ Map.lookup nm symFnEnv
    pcfg = (WPD.defaultConfig (symFromMaker fnmaker)){ WPD.cSymFnLookup = mklookup }
  WPD.SomeSymFn symFn <- liftIO $ do
    WPD.deserializeSymFnWithConfig pcfg symFnSexpr >>= \case
      Left err -> throwErr (err ++ "\n" ++ show symFnSexpr)
      Right result -> return result
  return $ SomeSome symFn

fnMakerFromEnv :: forall sym
                . WI.IsSymExprBuilder sym
               => sym
               -> SymFnEnv sym
               -> FunctionMaker sym
fnMakerFromEnv sym env  = FunctionMaker sym $ \formalName sig ->
  case Map.lookup formalName env of
    Just (SomeSome symFn) -> do
      Refl <- matchSigs sym sig symFn
      return $ Right symFn
    Nothing -> return $ Left $ "Missing expected formal function in environment: " ++ T.unpack formalName

-- | Deserialize a single What4 function, translating function calls according
-- to the given 'SymFnEnv'
deserializeSymFn :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                 => MonadFail m
                 => MonadIO m
                 => sym
                 -> SymFnEnv sym
                 -- ^ mapping from formal (locally-distinct) names to functions
                 -> SExpr
                 -> m (SomeSome (WI.SymFn sym))
deserializeSymFn sym env sexpr = deserializeSymFn' (fnMakerFromEnv sym env) sexpr

-- | Mapping informal (externally-visible) function names to functions
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

getSymFnEnv :: forall m. MonadFail m => SExpr -> m [(T.Text, SExpr)]
getSymFnEnv = \case
  S.L [ S.A (AId "SymFnEnv"), S.L symFnSExprs ] -> mapM go symFnSExprs
  x -> badSExpr x
  where
    go :: SExpr -> m (T.Text, SExpr)
    go = \case
      S.L [ S.A (AStr nm), symFnSExpr ] -> return (nm, symFnSExpr)
      x -> badSExpr x

-- | Deserialize a What4 function environment into the given 'env' type.
-- After each function is deserialized, it is added to the 'env' according
-- to the given function.
deserializeSymFnEnv' :: forall sym m env
                     . (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                    => MonadFail m
                    => MonadIO m
                    => sym
                    -> env
                    -- ^ initial value for the under-construction environment
                    -> (T.Text -> SomeSome (WI.SymFn sym) -> env -> m env)
                    -- ^ used to augment the environment after
                    -- each What4 function is deserialized
                    -> (env -> FunctionMaker sym)
                    -- ^ how to build a 'FunctionMaker' according to
                    -- the latest environment in order to interpret
                    -- function calls 
                    -> SExpr
                    -> m ([(T.Text, SomeSome (WI.SymFn sym))], env)
deserializeSymFnEnv' _sym env extendenv mkFun sexpr = do
  symFnSExprs <- getSymFnEnv sexpr
  (env', symFns) <- foldM go (env, []) symFnSExprs
  return $ (reverse $ symFns, env')
  where
    go :: (env, [(T.Text, SomeSome (WI.SymFn sym))])
       -> (T.Text, SExpr)
       -> m (env, [(T.Text, SomeSome (WI.SymFn sym))])
    go (env', symFns) (nm, symFnSExpr) = do
      symFn <- deserializeSymFn' (mkFun env') symFnSExpr
      env'' <- extendenv nm symFn env'
      return $ (env'', (nm, symFn) : symFns)

-- | Deserialize a What4 function environment with respect to
-- the given function binding environment 'NamedSymFnEnv'.
-- Each deserialized function is added to the environment, so
-- it is in-scope for subsequent functions.
deserializeSymFnEnv :: forall sym m
                     . (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                    => MonadFail m
                    => MonadIO m
                    => sym
                    -> NamedSymFnEnv sym
                    -> FunctionMaker sym
                    -> SExpr
                    -> m [(T.Text, SomeSome (WI.SymFn sym))]
deserializeSymFnEnv sym env mkFun' sexpr =
  fst <$> deserializeSymFnEnv' sym env (\nm symfn env' -> return $ Map.insert nm symfn env') mkFun sexpr
  where
    mkFun :: NamedSymFnEnv sym -> FunctionMaker sym
    mkFun env' = envFunctionMaker sym env' `composeMakers` mkFun'

-- | Compose two function makers together, attempting to use the first and
-- falling through to the second in the case of failure.
composeMakers :: FunctionMaker sym -> FunctionMaker sym -> FunctionMaker sym
composeMakers (FunctionMaker _ f1) (FunctionMaker sym f2) = FunctionMaker sym $ \nm sig ->
  f1 nm sig >>= \case
    Left _ -> f2 nm sig
    Right result -> return $ Right result

-- | Create a 'FunctionMaker' which looks up functions according to their
-- informal name in the given 'NamedSymFnEnv'.
envFunctionMaker :: (WI.IsSymExprBuilder sym)
                 => sym
                 -> NamedSymFnEnv sym
                 -> FunctionMaker sym
envFunctionMaker sym env = FunctionMaker sym $ \_nm sig ->
  lookupFnSig sym env sig >>= \case
      Just symFn -> return $ Right symFn
      Nothing -> return $ Left $ "Missing function for signature: " ++ show sig

type LazySymFnEnv sym = (Map T.Text SExpr, IO.IORef (Map T.Text (SomeSome (WI.SymFn sym))))

-- | Create a 'FunctionMaker' which lazily deserializes from
-- the given environment (mapping informal names to s-expressions), and
-- caches the result using the given 'IO.IORef'.
lazyFunctionMaker :: (WI.IsSymExprBuilder sym, sym ~ WB.ExprBuilder t st fs, ShowF (WB.SymExpr sym))
                  => sym
                  -> LazySymFnEnv sym
                  -> FunctionMaker sym
                  -- ^ maker used when deserializing functions from the given environment
                  -> FunctionMaker sym
lazyFunctionMaker sym (env, ref) fallthrough = do
  FunctionMaker sym $ \_formalName sig -> do
    nmedEnv <- liftIO $ IO.readIORef ref
    lookupFnSig sym nmedEnv sig >>= \case
      Just symFn -> return $ Right symFn
      Nothing -> case Map.lookup (fsName sig) env of
        Just sexpr -> do
          let recursiveMaker = lazyFunctionMaker sym (env, ref) fallthrough `composeMakers` fallthrough
          SomeSome symFn <- deserializeSymFn' recursiveMaker sexpr
          Refl <- matchSigs sym sig symFn
          Right <$> (liftIO $ expandSymFn sym symFn)
        _ -> return $ Left $ "Missing function in environment for: " ++ show sig

mapFunctionMaker :: (forall args ret. sym -> WI.SymFn sym args ret -> IO (WI.SymFn sym args ret))
                 -> FunctionMaker sym
                 -> FunctionMaker sym
mapFunctionMaker g (FunctionMaker sym f) = FunctionMaker sym $ \nm sig -> f nm sig >>= \case
  Left err -> fail err
  Right result -> Right <$> (liftIO $ g sym result)

-- | Swap out the "unfold" condition for a function to be always true.
expandSymFn :: sym ~ WB.ExprBuilder t st fs
            => sym
            -> WB.ExprSymFn t args ret
            -> IO (WB.ExprSymFn t args ret)
expandSymFn sym symFn = case WB.symFnInfo symFn of
  WB.DefinedFnInfo args expr _ -> WI.definedFn sym (WB.symFnName symFn) args expr (\_ -> True)
  _ -> return symFn

-- | Create a 'FunctionMaker' which creates a uninterpreted functions matching the
-- given signature.
uninterpFunctionMaker :: forall sym. WI.IsSymExprBuilder sym => sym -> FunctionMaker sym
uninterpFunctionMaker sym = FunctionMaker sym $ \_nm sig -> do
  Right <$> (liftIO $ WI.freshTotalUninterpFn sym (U.makeSymbol (T.unpack (fsName sig))) (fsArgs sig) (fsRet sig))

-- | Create a 'FunctionMaker' which never creates any functions.
noFunctionMaker :: forall sym. WI.IsSymExprBuilder sym => sym -> FunctionMaker sym
noFunctionMaker sym = FunctionMaker sym $ \_ _ -> return $ Left "noFunctionMaker called"

-- | A 'FunctionMaker' combinator which uses the first maker if the
-- given predicate evaluates to true, and the second otherwise.
iteFunctionMaker :: WI.IsSymExprBuilder sym
                 => (forall args ret. T.Text -> FunSig args ret -> Bool)
                 -> FunctionMaker sym
                 -> FunctionMaker sym
                 -> FunctionMaker sym
iteFunctionMaker filt (FunctionMaker sym f) (FunctionMaker _ g) = FunctionMaker sym $ \formalName sig -> do
  case (filt formalName sig) of
    True -> f formalName sig
    False -> g formalName sig
