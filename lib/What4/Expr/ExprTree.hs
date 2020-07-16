{-|
Module           : Language.ASL.Formulas.ExprTree
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Functions for manipulating what4 expressions containing
nested structs.


-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module What4.Expr.ExprTree
  ( HasExprBuilder(..)
  , SomeExprBuilder(..)
  , ExprNormOps(..)
  , BaseTypeTree(..)
  , NormBaseTypeCtx
  , NormBaseType
  , generateTree
  , collapseTree
  , flatExpr
  , flatExprIO
  , normExprVars
  , normExprVarsIO
  , withExprBuilder
  , withExprBuilder'
  , normFieldAccs
  -- FIXME: move
  , forWithIndex
  ) where

import           Data.Kind
import           Data.Proxy

import           Control.Monad
import qualified Control.Monad.Trans.Reader as MR hiding ( reader, local, ask, asks )
import qualified Control.Monad.Reader as MR
import qualified Control.Monad.IO.Class as IO
import qualified Control.Monad.IO.Unlift as IO
import qualified Data.Text as T

import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Classes

import qualified What4.Symbol as WI
import qualified What4.Interface as WI
import qualified What4.Expr.Builder as WB

-- from this package
import           Data.Parameterized.CtxFuns
import           Data.Parameterized.AssignTree
import qualified Data.Parameterized.AssignTree as AT

-- | Project a 'WI.BaseType' to a 'CtxTree', reflecting nested struct
-- types and where the tree elements are non-struct types.
type family AsBaseTypeTree (tp :: WI.BaseType) :: CtxTree WI.BaseType where
  AsBaseTypeTree (WI.BaseStructType ctx) = CtxBranch (MapCtx AsBaseTypeTreeWrapper ctx)
  AsBaseTypeTree tp = CtxLeaf tp

-- | Normalize a 'WI.BaseType' by flattening it into a one-dimensional struct
-- and applying the given type-level function to each field type
type NormBaseType f tp = WI.BaseStructType (FlattenCtxTree (MapCtxTree f (AsBaseTypeTree tp)))

-- | Normalize a 'Ctx WI.BaseType' by flattening each type and concatenating the result
type NormBaseTypeCtx f ctx = MapCtx f (FlattenCtxTree (CtxBranch (MapCtx AsBaseTypeTreeWrapper ctx)))

data BaseTypeTreeRepr tp ttp where
  BaseTypeTreeBranch :: Assignment WI.BaseTypeRepr ctx
                     -> BaseTypeTreeRepr (WI.BaseStructType ctx) (CtxBranch (MapCtx AsBaseTypeTreeWrapper ctx))
  BaseTypeTreeLeaf :: WI.BaseTypeRepr tp -> BaseTypeTreeRepr tp (CtxLeaf tp)


baseTreeRepr :: WI.BaseTypeRepr tp
             -> BaseTypeTreeRepr tp (AsBaseTypeTree tp)
baseTreeRepr repr = case repr of
  WI.BaseStructRepr reprs -> BaseTypeTreeBranch reprs
  WI.BaseBoolRepr -> BaseTypeTreeLeaf repr
  WI.BaseBVRepr _ -> BaseTypeTreeLeaf repr
  WI.BaseNatRepr -> BaseTypeTreeLeaf repr
  WI.BaseIntegerRepr -> BaseTypeTreeLeaf repr
  WI.BaseRealRepr -> BaseTypeTreeLeaf repr
  WI.BaseFloatRepr _ -> BaseTypeTreeLeaf repr
  WI.BaseStringRepr _ -> BaseTypeTreeLeaf repr
  WI.BaseComplexRepr -> BaseTypeTreeLeaf repr
  WI.BaseArrayRepr _ _ -> BaseTypeTreeLeaf repr

data BaseStructWrapper :: TyFun (Ctx WI.BaseType) WI.BaseType -> Type
type instance Apply BaseStructWrapper ctx = WI.BaseStructType ctx

data AsBaseTypeTreeWrapper :: TyFun WI.BaseType (CtxTree WI.BaseType) -> Type
type instance Apply AsBaseTypeTreeWrapper t = AsBaseTypeTree t


collapseEqs :: Assignment WI.BaseTypeRepr ctx -> CollapseCtxTree BaseStructWrapper (CtxBranch (MapCtx AsBaseTypeTreeWrapper ctx)) :~: WI.BaseStructType ctx
collapseEqs reprs = case viewAssign reprs of
  AssignExtend reprs' repr | Refl <- collapseEqs reprs', Refl <- collapseEq repr -> Refl
  AssignEmpty -> Refl

collapseEq :: WI.BaseTypeRepr tp -> CollapseCtxTree BaseStructWrapper (AsBaseTypeTree tp) :~: tp
collapseEq repr = case baseTreeRepr repr of
  BaseTypeTreeBranch reprs -> collapseEqs reprs
  BaseTypeTreeLeaf _ -> Refl


data BaseTypeTree f tp where
  BaseTypeTree :: WI.BaseTypeRepr tp -> AssignTree f (AsBaseTypeTree tp) -> BaseTypeTree f tp

baseTypeTreeRepr :: BaseTypeTree f tp
                 -> WI.BaseTypeRepr tp
baseTypeTreeRepr (BaseTypeTree repr _) = repr

branchTrees :: Assignment (BaseTypeTree f) ctx
            -> BaseTypeTree f (WI.BaseStructType ctx)
branchTrees trees =
  let
    trees' = applyMapCtx (Proxy @AsBaseTypeTreeWrapper) (\(BaseTypeTree _ tree) -> tree) trees
    repr = WI.BaseStructRepr $ FC.fmapFC baseTypeTreeRepr trees
  in BaseTypeTree repr (AssignTreeBranch trees')


data ExprTreeEnv t where
  ExprTreeEnv :: { etToTreeCache :: WB.IdxCache t (BaseTypeTree (WB.Expr t))
                 , _etBuilder :: WB.ExprBuilder t st fs
                 } -> ExprTreeEnv t

newtype ExprTreeM t a =
  ExprTreeM { _unET :: (MR.ReaderT (ExprTreeEnv t) IO) a }
  deriving ( Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MR.MonadReader (ExprTreeEnv t)
           )

instance HasExprBuilder t (ExprTreeM t) where
  getExprBuilder = do
    ExprTreeEnv _ sym <- MR.ask
    return $ SomeExprBuilder sym

evalExprTreeM :: WB.ExprBuilder t st fs -> ExprTreeM t a -> IO a
evalExprTreeM sym (ExprTreeM f) = do
  toTreeCache <- WB.newIdxCache
  MR.runReaderT f (ExprTreeEnv toTreeCache sym)


-- | Expand expression into an 'AssignTree' over its nested fields.
-- Expressions in tree leaves are necessarily non-struct types, however they may
-- themselves contain nested structs that are the result of unevaluated functions calls
-- or free variables
exprToTree :: forall t tp
            . WB.Expr t tp
           -> ExprTreeM t (BaseTypeTree (WB.Expr t) tp)
exprToTree e = do
  cache <- MR.asks etToTreeCache
  case WB.exprMaybeId e of
    Just idx -> IO.liftIO (WB.lookupIdx cache idx) >>= \case
      Just tree -> return tree
      Nothing -> do
        e' <- go
        IO.liftIO $ WB.insertIdxValue cache idx e'
        return e'
    Nothing -> go
  where
    go :: ExprTreeM t (BaseTypeTree (WB.Expr t) tp)
    go = case WB.asApp e of
      Just (WB.StructCtor _ flds) -> branchTrees <$> FC.traverseFC exprToTree flds
      Just (WB.StructField struct idx _) -> exprToTree struct >>= \case
        BaseTypeTree _ (AssignTreeBranch trees) ->
          let
            WI.BaseStructRepr reprs = WI.exprType struct
            idx' = mapCtxIndex (Proxy @AsBaseTypeTreeWrapper) (size reprs) idx
          in return $ BaseTypeTree (WI.exprType e) $ trees ! idx'
      Just (WB.BaseIte repr _ test then_ else_) -> do
        BaseTypeTree _ thenTree <- exprToTree then_
        BaseTypeTree _ elseTree <- exprToTree else_
        trees <- AT.zipWithM (\then' else' -> withSym $ \sym -> WI.baseTypeIte sym test then' else') thenTree elseTree
        return $ BaseTypeTree repr trees
      _ -> withSym $ \sym -> generateTree WI.exprType (WI.structField sym) e

forWithIndex :: Applicative m
             => Assignment f ctx
             -> (forall tp. Index ctx tp -> f tp -> m (g tp))
             -> m (Assignment g ctx)
forWithIndex asn f = traverseWithIndex f asn

generateTree :: Monad m
             => (forall tp'. f tp' -> WI.BaseTypeRepr tp')
             -> (forall ctx tp'. f (WI.BaseStructType ctx) -> Index ctx tp' -> m (f tp'))
             -> f tp
             -> m (BaseTypeTree f tp)
generateTree getrepr f e = case baseTreeRepr (getrepr e) of
  BaseTypeTreeBranch reprs -> do
    liftM branchTrees $ forWithIndex reprs $ \idx _ -> do
      a <- f e idx
      generateTree getrepr f a
  BaseTypeTreeLeaf _ -> return $ BaseTypeTree (getrepr e) (AssignTreeLeaf e)

collapseTree :: Monad m
             => (forall tp'. f tp' -> m (g tp'))
             -> (forall ctx. Assignment g ctx -> m (g (WI.BaseStructType ctx)))
             -> BaseTypeTree f tp
             -> m (g tp)
collapseTree g f (BaseTypeTree repr tree)
  | Refl <- collapseEq repr = collapseAssignTree (Proxy @BaseStructWrapper) g f tree

appendToSymbol ::  WI.SolverSymbol -> String -> WI.SolverSymbol
appendToSymbol symbol str =
  let
    symbolstr = T.unpack $ WI.solverSymbolAsText symbol
  in WI.safeSymbol (symbolstr ++ str)


-- | An invertable monadic type-changing expression transformer
data ExprNormOps f t m =
  ExprNormOps { normExprLeaf :: forall tp'. WB.Expr t tp' -> m (WB.Expr t (Apply f tp'))
              , unNormExpr :: forall tp'. WI.BaseTypeRepr tp' -> WB.Expr t (Apply f tp') -> m (WB.Expr t tp')
              , normRepr :: forall tp'. WI.BaseTypeRepr tp' -> WI.BaseTypeRepr (Apply f tp')
              }

unliftIOExprOps :: forall m f t
                 . IO.MonadIO m => ExprNormOps f t IO -> ExprNormOps f t m
unliftIOExprOps ops =
  let
    normExprLeaf' :: forall tp'. WB.Expr t tp' -> m (WB.Expr t (Apply f tp'))
    normExprLeaf' e = IO.liftIO (normExprLeaf ops e)

    unNormExpr' :: forall tp'. WI.BaseTypeRepr tp' -> WB.Expr t (Apply f tp') -> m (WB.Expr t tp')
    unNormExpr' repr e = IO.liftIO (unNormExpr ops repr e)
  in ExprNormOps normExprLeaf' unNormExpr' (normRepr ops)

data SomeExprBuilder t where
  SomeExprBuilder :: WB.ExprBuilder t st fs -> SomeExprBuilder t

-- | A type class indicating that a monad wraps a 'WB.ExprBuilder'
class IO.MonadIO m => HasExprBuilder t m where
  getExprBuilder :: m (SomeExprBuilder t)

  withSym :: (forall st fs. WB.ExprBuilder t st fs -> IO a) -> m a
  withSym f = do
    SomeExprBuilder sym <- getExprBuilder
    IO.liftIO $ f sym

newtype ExprBuilderM t a = ExprBuilderM (MR.ReaderT (SomeExprBuilder t) IO a)
  deriving (Functor, Applicative, Monad, IO.MonadIO, IO.MonadUnliftIO, MR.MonadReader (SomeExprBuilder t))

instance HasExprBuilder t (ExprBuilderM t) where
  getExprBuilder = MR.ask

evalExperBuilderM :: WB.ExprBuilder t st fs -> ExprBuilderM t a -> IO a
evalExperBuilderM sym (ExprBuilderM f) = MR.runReaderT f (SomeExprBuilder sym)

withExprBuilder :: WB.ExprBuilder t st fs -> (forall m. HasExprBuilder t m => m a) -> IO a
withExprBuilder sym f = evalExperBuilderM sym f

unliftHasBuilder :: Functor g
                 => (forall m. HasExprBuilder t m => IO.MonadUnliftIO m => m (g (m a)))
                 -> ExprBuilderM t (g (IO a))
unliftHasBuilder f = do
  ret <- f
  g <- IO.askRunInIO
  return $ fmap g ret

withExprBuilder' :: forall g t st fs a
                  . Functor g
                 => WB.ExprBuilder t st fs
                 -> (forall m. HasExprBuilder t m => IO.MonadUnliftIO m => m (g (m a)))
                 -> IO (g (IO a))
withExprBuilder' sym f = evalExperBuilderM sym (unliftHasBuilder f)

-- | Flatten an expression of a nested struct type into a 1-dimensional struct, applying
-- the given type-changing normalization function to each atomic field. Returns an inversion
-- function to take expressions from the normalized type back to the original type.
flatExpr :: forall m f t tp
          . HasExprBuilder t m
         => ExprNormOps f t m
         -> WB.Expr t tp
         -> m (WB.Expr t (NormBaseType f tp), WB.Expr t (NormBaseType f tp) -> m (WB.Expr t tp))
flatExpr nops e = do
  BaseTypeTree _ tree <- withSym $ \sym -> evalExprTreeM sym (exprToTree e)
  tree' <- traverseMapCtxTree (Proxy @f) (normExprLeaf nops) tree
  flatTrees <- return $ flattenAsnTree tree'
  struct <- withSym $ \sym -> WI.mkStruct sym flatTrees
  let unflatten struct' =
        collapseUnflatten (Proxy @BaseStructWrapper) (Proxy @f) (getField struct')
          (\flds -> withSym $ \sym -> WI.mkStruct sym flds) tree tree'
  Refl <- return $ collapseEq (WI.exprType e)
  return (struct, unflatten)
  where
    getField :: forall tp'
              . WB.Expr t (NormBaseType f tp)
             -> Index (FlattenCtxTree (MapCtxTree f (AsBaseTypeTree tp))) (Apply f tp')
             -> WB.Expr t tp'
             -> WB.Expr t (Apply f tp')
             -> m (WB.Expr t tp')
    getField struct idx e' _ = do
      fld <- withSym $ \sym -> WI.structField sym struct idx
      (unNormExpr nops) (WI.exprType e') fld

newtype NormExprRet t f tp a where
  NormExprRet :: (WB.Expr t (NormBaseType f tp), WB.Expr t (NormBaseType f tp) -> a) -> NormExprRet t f tp a
  deriving Functor

-- | Specialized 'flatExpr' to 'IO'
flatExprIO :: forall sym st fs tp f t
            . sym ~ WB.ExprBuilder t st fs
           => sym
           -> ExprNormOps f t IO
           -> WB.Expr t tp
           -> IO (WB.Expr t (NormBaseType f tp), WB.Expr t (NormBaseType f tp) -> IO (WB.Expr t tp))
flatExprIO sym nops e = do
  NormExprRet ret <- withExprBuilder' sym (NormExprRet @t @f @tp <$> flatExpr (unliftIOExprOps nops) e)
  return ret

data Applied f g tp where
  Applied :: WI.BaseTypeRepr tp -> g (Apply f tp) -> Applied f g tp

-- | Project a tree of bound variables reflecting the type of a given bound variable.
getBoundVarsTree :: forall f t tp m
                  . HasExprBuilder t m
                 => ExprNormOps f t m
                 -> WB.ExprBoundVar t tp
                 -> m (PairF (WB.Expr t) (BaseTypeTree (Applied f (WB.ExprBoundVar t))) tp)
getBoundVarsTree nops bv = do
  apbv <- mkBVar bv
  freshBVTree <- generateTree (\(Applied repr _) -> repr) mkSubBVar apbv
  freshStruct <- collapseTree unApply (\flds -> withSym $ \sym -> WI.mkStruct sym flds) freshBVTree
  return $ PairF freshStruct freshBVTree
  where
    unApply :: forall tp'
             . Applied f (WB.ExprBoundVar t) tp'
            -> m (WB.Expr t tp')
    unApply (Applied repr bv') = do
      e <- withSym $ \sym -> return $ WI.varExpr sym bv'
      unNormExpr nops repr e

    mkBVar :: forall tp'
            . WB.ExprBoundVar t tp'
           -> m (Applied f (WB.ExprBoundVar t) tp')
    mkBVar bv' = do
      let
        nm = (WB.bvarName bv') `appendToSymbol` "_norm"
        repr = WB.bvarType bv'
        repr' = normRepr nops repr
      Applied repr <$> (withSym $ \sym -> WI.freshBoundVar sym nm repr')

    mkSubBVar :: forall ctx tp'
               . Applied f (WB.ExprBoundVar t) (WI.BaseStructType ctx)
              -> Index ctx tp'
              -> m (Applied f (WB.ExprBoundVar t) tp')
    mkSubBVar (Applied (WI.BaseStructRepr reprs) bv') idx = do
      let
        repr = reprs ! idx
        repr' = normRepr nops repr
        nm = (WB.bvarName bv') `appendToSymbol` ("_" ++ show (indexVal idx))
      Applied repr <$> (withSym $ \sym -> WI.freshBoundVar sym nm repr')


-- | Replace bound variables in the given term with fresh variables, producing
-- distinct variables for the fields in each struct-typed variable, and producing normalized-typed
-- variables (which are un-normalized back into the original expression).
normExprVars :: forall f t m ctx tp
              . HasExprBuilder t m
             => ExprNormOps f t m
             -> Assignment (WB.ExprBoundVar t) ctx
             -> WB.Expr t tp
             -> m ( WB.Expr t tp
                  , Assignment (WB.ExprBoundVar t) (NormBaseTypeCtx f ctx)
                  , Assignment (WB.Expr t) ctx -> m (Assignment (WB.Expr t) (NormBaseTypeCtx f ctx)))
normExprVars nops bvs expr = do
  (structExprs, vartrees) <- unzipPairF <$> FC.traverseFC (getBoundVarsTree nops) bvs
  expr' <- withSym $ \sym -> WB.evalBoundVars sym expr bvs structExprs
  let
    varTrees' = applyMapCtx (Proxy @AsBaseTypeTreeWrapper) (\(BaseTypeTree _ tree) -> tree) vartrees
    flatVarTree = flattenAsnTree (AssignTreeBranch varTrees')
    appliedVarTree = applyMapCtx (Proxy @f) (\(Applied _ bv) -> bv) flatVarTree

    flatArg :: forall tp'. WB.Expr t tp' -> m (AssignTree (WB.Expr t) (AsBaseTypeTree tp'))
    flatArg e = do
      BaseTypeTree _ tree <- withSym $ \sym -> evalExprTreeM sym (exprToTree e)
      return tree

    normArgs :: Assignment (WB.Expr t) ctx -> m (Assignment (WB.Expr t) (NormBaseTypeCtx f ctx))
    normArgs args = do
      trees <- traverseMapCtx (Proxy @AsBaseTypeTreeWrapper) flatArg args
      flat <- return $ flattenAsnTrees trees
      traverseMapCtx (Proxy @f) (normExprLeaf nops) flat

  return (expr', appliedVarTree, normArgs)

newtype NormExprVarsRet t f tp ctx a where
  NormExprVarsRet :: ( WB.Expr t tp
                     , Assignment (WB.ExprBoundVar t) (NormBaseTypeCtx f ctx)
                     , Assignment (WB.Expr t) ctx -> a)
                     -> NormExprVarsRet t f tp ctx a
  deriving Functor

normExprVarsIO :: forall sym st fs f t ctx tp
                . sym ~ WB.ExprBuilder t st fs
               => sym
               -> ExprNormOps f t IO
               -> Assignment (WB.ExprBoundVar t) ctx
               -> WB.Expr t tp
               -> IO ( WB.Expr t tp
                     , Assignment (WB.ExprBoundVar t) (NormBaseTypeCtx f ctx)
                     , Assignment (WB.Expr t) ctx -> IO (Assignment (WB.Expr t) (NormBaseTypeCtx f ctx)))
normExprVarsIO sym nops bvs expr = do
  NormExprVarsRet ret <- withExprBuilder' sym (NormExprVarsRet @t @tp @f <$> normExprVars (unliftIOExprOps nops) bvs expr)
  return ret


-- | normalize struct field accesses to reduce across if-then-else expressions.
-- i.e. (field 1 (ite b (W X) (Y Z))) --> (ite b W Y)
normFieldAccs :: forall sym st fs t tp
               . sym ~ WB.ExprBuilder t st fs
              => sym
              -> WB.Expr t tp
              -> IO (WB.Expr t tp)
normFieldAccs sym e = do
  cache <- WB.newIdxCache
  normFieldAccs' sym cache e

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
        let a = WB.appExprApp appExpr
        ap' <- WB.traverseApp (normFieldAccs' sym cache) a
        let ret = if a == ap' then return e else WB.sbMakeExpr sym ap'
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
    goApp ret a = case a of
      (WB.StructCtor _ flds) -> do
        flds' <- traverseWithIndex (\idx _ -> normField sym cache e idx) flds
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
          -> Index ctx tp
          -> IO (WB.Expr t tp)
normField sym cache e idx = normField' sym cache e idx >>= \case
  Just e' -> return e'
  Nothing -> WI.structField sym e idx


normField' :: forall sym st fs t ctx tp
           . sym ~ WB.ExprBuilder t st fs
          => sym
          -> WB.IdxCache t (WB.Expr t)
          -> WB.Expr t (WI.BaseStructType ctx)
          -> Index ctx tp
          -> IO (Maybe (WB.Expr t tp))
normField' sym cache e idx = case e of
  WB.AppExpr appExpr' -> case (WB.appExprApp appExpr') of
    WB.StructField e' idx' _  -> do
      e'' <- normFieldAccs' sym cache e'
      normField' sym cache e'' idx' >>= \case
        Just fld -> normField' sym cache fld idx
        Nothing -> return Nothing

    WB.StructCtor _ flds -> Just <$> (normFieldAccs' sym cache $ flds ! idx)
    WB.BaseIte _ _ test then_ else_ -> do
      test' <- normFieldAccs' sym cache test
      then' <- normField sym cache then_ idx
      else' <- normField sym cache else_ idx
      Just <$> (WI.baseTypeIte sym test' then' else')
    _ -> return Nothing
  _ -> return Nothing
