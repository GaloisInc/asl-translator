{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.ASL.Globals.Types
  ( Global(..)
  , GlobalDomain(..)
  , GlobalsType
  , domainSingleton
  , domainUnbounded
  , asSingleton
  , mkGlobalsTypeInstDecls
  , mkAllGlobalSymsT
  , mkTypeFromGlobals
  , mkTypeFromReprs
  , genCond
  , mkGlobalsT
  , mkGlobalsE
  , mkSymbolE
  , mkSymbolT
  , forallSymbols
  , forallNats
  -- statically calculating indexes
  , KnownIndex
  , knownIndex
  , withKnownIndex
  , NotMemberOf
  , DistinctIn
  , DistinctCtx
  , ForallCtx
  , mapForallCtx
  , traverseForallCtx
  , forallUpTo
  ) where


import           GHC.TypeLits

import           Control.Applicative ( Const(..) )

import qualified Control.Monad.Except as ME
import           Control.Monad.Identity

import           Data.Type.Equality
import           Data.Constraint as Constraint
import           Data.Proxy

import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Context ( pattern (:>) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableFC as FC


import           Data.Maybe ( catMaybes )
import           Data.List ( intercalate )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Text as T
import           Data.Parameterized.NatRepr ( type (<=) )
import qualified What4.Interface as WI
import qualified What4.Concrete as WI

-- from this package
import           Data.Parameterized.CtxFuns

import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT

import           Language.ASL.Types

import qualified Language.Haskell.TH as TH

-- | A 'Global' represents each piece of the global ASL state.
data Global tp =
  Global
    { gbName :: T.Text
    -- ^ The name of the ASL global variable that this corresponds to
    , gbType :: WI.BaseTypeRepr tp
    -- ^ The translated base type of this global variable
    , gbDomain :: GlobalDomain tp
    -- ^ The known domain of this global variable
    -- Every update to this value needs to check that this domain has been respected.
    }

instance TestEquality Global where
  testEquality (Global nm tp dm) (Global nm' tp' dm') =
    case testEquality tp tp' of
      Just Refl | nm == nm' && dm == dm' -> Just Refl
      _ -> Nothing

data GlobalDomain tp =
    DomainSet (Set (WI.ConcreteVal tp))
    -- ^ the global is one of a fixed set of values
  | DomainSpan (Maybe (WI.ConcreteVal tp)) (Maybe (WI.ConcreteVal tp))
    -- ^ the global is in a range of values (inclusive). A 'Nothing' bound indicates
    -- it is unbounded in that direction.
  deriving Eq

domainSingleton :: WI.ConcreteVal tp -> GlobalDomain tp
domainSingleton v = DomainSet (Set.singleton v)

domainUnbounded :: GlobalDomain tp
domainUnbounded = DomainSpan Nothing Nothing


domainSpan :: GlobalDomain tp -> (Maybe (WI.ConcreteVal tp), Maybe (WI.ConcreteVal tp))
domainSpan dom = case dom of
  DomainSet s | Set.size s == 1, [x] <- Set.toList s -> (Just x, Just x)
  DomainSpan lo hi -> (lo, hi)
  _ -> (Nothing, Nothing)

asSingleton :: GlobalDomain tp -> Maybe (WI.ConcreteVal tp)
asSingleton dom = case domainSpan dom of
  (Just lo, Just hi) | lo == hi -> Just lo
  _ -> Nothing

genLeq :: WI.BaseTypeRepr tp
       -> CCG.Expr ext s (CT.BaseToType tp)
       -> CCG.Expr ext s (CT.BaseToType tp)
       -> CCG.Expr ext s CT.BoolType
genLeq repr e1 e2 = CCG.App $ case repr of
  WI.BaseIntegerRepr -> CCE.IntLe e1 e2
  WI.BaseBVRepr nr -> CCE.BVUle nr e1 e2
  _ -> error $ "Cannot compare values of type:" ++ show repr

concreteToExpr :: WI.ConcreteVal tp
               -> CCG.Expr ext s (CT.BaseToType tp)
concreteToExpr cv = CCG.App $ case cv of
  WI.ConcreteBool b -> CCE.BoolLit b
  WI.ConcreteInteger i -> CCE.IntLit i
  WI.ConcreteBV nr i -> CCE.BVLit nr i
  _ -> error "unsupported concrete value"

domainPred :: forall ext s tp
            . Global tp
           -> CCG.Expr ext s (CT.BaseToType tp)
           -> CCG.Expr ext s CT.BoolType
domainPred gb e = case gbDomain gb of
  DomainSet vs -> foldr go (CCG.App $ CCE.BoolLit False) vs
    where
      go :: WI.ConcreteVal tp -> CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType
      go v pred_ =
        let
          e' = concreteToExpr v
          isEq = CCG.App $ CCE.BaseIsEq (WI.concreteType v) e e'
        in mkOr isEq pred_
  DomainSpan lo hi ->
    let
      loPred = case lo of
        Just loVal -> genLeq (gbType gb) (concreteToExpr loVal) e
        Nothing -> CCG.App $ CCE.BoolLit True
      hiPred = case hi of
        Just hiVal -> genLeq (gbType gb) e (concreteToExpr hiVal)
        Nothing -> CCG.App $ CCE.BoolLit True
    in mkAnd loPred hiPred

mkOr :: CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType
mkOr e1 e2 = case (e1, e2) of
   (CCG.App (CCE.BoolLit False), _) -> e2
   (_, CCG.App (CCE.BoolLit False)) -> e1
   _ -> CCG.App $ CCE.Or e1 e2

mkAnd :: CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType
mkAnd e1 e2 = case (e1, e2) of
   (CCG.App (CCE.BoolLit True), _) -> e2
   (_, CCG.App (CCE.BoolLit True)) -> e1
   _ -> CCG.App $ CCE.And e1 e2


projectGlobals :: forall m ctx
                . (Monad m, ME.MonadError String m)
               => Map T.Text (Some Global)
               -> Ctx.Assignment (LabeledValue T.Text WI.BaseTypeRepr) ctx
               -> m (Ctx.Assignment Global ctx)
projectGlobals globalsMap sig = do
  errs <- FC.toListFC (\(Const s) -> s) <$> FC.traverseFC tryGetGlobal sig
  let allerr = intercalate ['\n'] (catMaybes errs)
  FC.traverseFC (\lblv -> getGlobal lblv `ME.catchError` (\_ -> ME.throwError allerr)) sig
  where
    tryGetGlobal :: forall tp. LabeledValue T.Text WI.BaseTypeRepr tp
                 -> m (Const (Maybe String) tp)
    tryGetGlobal lblv =
      ((\_ -> Const Nothing) <$> getGlobal lblv) `ME.catchError` (\err -> return $ Const $ Just $ err)

    getGlobal :: forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> m (Global tp)
    getGlobal lblv = case Map.lookup (projectLabel lblv) globalsMap of
      Just (Some gb) | Just Refl <- testEquality (projectValue lblv) (gbType gb)
        -> return $ gb
      _ -> ME.throwError $ "Missing global specification for: "
        ++ T.unpack (projectLabel lblv) ++ " " ++ show (projectValue lblv)


genCond :: forall ext s ctx err m
         . (Monad m, ME.MonadError err m)
        => (String -> err)
        -> Map T.Text (Some Global)
        -> (forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> m (CCG.Expr ext s (CT.BaseToType tp)))
        -> Ctx.Assignment (LabeledValue T.Text WI.BaseTypeRepr) ctx
        -> m [(T.Text, CCG.Expr ext s CT.BoolType)]
genCond mkerr globalsMap lookup_ sig = do
  globals <- case projectGlobals globalsMap sig of
    Left errStr -> ME.throwError $ mkerr errStr
    Right globals -> return globals
  filter isNonTrivial . FC.toListFC (\(Const e1) -> e1) <$> Ctx.zipWithM getPred sig globals
  where
    isNonTrivial :: (T.Text, CCG.Expr ext s CT.BoolType) -> Bool
    isNonTrivial (_, CCG.App (CCE.BoolLit True)) = False
    isNonTrivial _ = True

    getPred :: forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> Global tp -> m (Const (T.Text, (CCG.Expr ext s CT.BoolType)) tp)
    getPred lblv gb = do
      expr <- lookup_ lblv
      return $ Const $ (projectLabel lblv, domainPred gb expr)

-- Retrieving indexes into the globals based on type-level symbols

-- | The type-level mapping from name of each global to its type
type family GlobalsType (s :: Symbol) :: WI.BaseType

-- Template haskell for reifying the types and names from 'Language.ASL.Globals.Types'

mkGlobalsGen :: forall a
              . (a -> a -> TH.Q a)
             -> TH.Q a
             -> (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q a)
             -> Some (Ctx.Assignment Global)
             -> TH.Q a
mkGlobalsGen comb mkinit mkelem (Some gbs) = do
  elems <- Ctx.traverseWithIndex go gbs
  init_ <- mkinit
  FC.foldlMFC (\b (Const a) -> comb b a) init_ elems
  where
    go :: Ctx.Index ctx tp -> Global tp -> TH.Q (Const a tp)
    go idx gb = Const <$> mkelem idx gb

mkGlobalsE :: (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q TH.Exp)
           -> Some (Ctx.Assignment Global)
           -> TH.Q TH.Exp
mkGlobalsE = mkGlobalsGen (\b a -> [e| $(return b) Ctx.:> $(return a) |]) [e| Ctx.empty |]

mkGlobalsT :: (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q TH.Type)
           -> Some (Ctx.Assignment Global)
           -> TH.Q TH.Type
mkGlobalsT = mkGlobalsGen (\b a -> [t| $(return b) Ctx.::> $(return a) |]) [t| Ctx.EmptyCtx |]

-- | T.Text -> [t| Symbol |]
mkSymbolT :: T.Text -> TH.Q TH.Type
mkSymbolT nm = TH.litT (TH.strTyLit (T.unpack $ nm))

-- | T.Text -> [e| CT.SymbolRepr |]
mkSymbolE :: T.Text -> TH.Q TH.Exp
mkSymbolE nm = [e| CT.knownSymbol :: CT.SymbolRepr $(mkSymbolT nm) |]

mkGlobalsDecls' :: (forall ctx tp. Ctx.Index ctx tp -> Global tp -> TH.DecsQ) -> Some (Ctx.Assignment Global) -> TH.DecsQ
mkGlobalsDecls' f = mkGlobalsGen (\b a -> return $ b ++ a) (return []) f

mkGlobalsDecls :: (forall tp. Global tp -> TH.DecsQ) -> Some (Ctx.Assignment Global) -> TH.DecsQ
mkGlobalsDecls f = mkGlobalsDecls' (\_ -> f)

mkGlobalsTypeInstDecls :: Some (Ctx.Assignment Global) -> TH.DecsQ
mkGlobalsTypeInstDecls = mkGlobalsDecls $ \gb ->
  [d| type instance GlobalsType $(mkSymbolT (gbName gb)) = $(mkTypeFromRepr (gbType gb)) |]

forallGen :: (forall tp. f tp -> TH.Q TH.Type)
          -> TH.Q TH.Type
          -> Ctx.Assignment f ctx
          -> TH.DecsQ
forallGen mktype inst asn = case Ctx.viewAssign asn of
  Ctx.AssignEmpty -> return []
  Ctx.AssignExtend asn' a -> do
    decl <- TH.instanceD (return []) (TH.appT inst (mktype a)) []
    decls <- forallGen mktype inst asn'
    return $ decl : decls

forallSymbols :: TH.Q TH.Type -> Ctx.Assignment CT.SymbolRepr ctx -> TH.DecsQ
forallSymbols = forallGen (\symb -> mkSymbolT (CT.symbolRepr symb))

forallNats ::  TH.Q TH.Type -> Ctx.Assignment NR.NatRepr ctx -> TH.DecsQ
forallNats = forallGen (\nr -> TH.litT (TH.numTyLit (NR.intValue nr)))

mkAllGlobalSymsT :: Some (Ctx.Assignment Global) -> TH.Q TH.Type
mkAllGlobalSymsT = mkGlobalsT $ \_ gb -> mkSymbolT (gbName gb)

mkTypeFromGlobals :: Some (Ctx.Assignment Global) -> TH.Q TH.Type
mkTypeFromGlobals = mkGlobalsT $ \_ gb -> mkTypeFromRepr (gbType gb)

mkTypeFromRepr :: WI.BaseTypeRepr tp -> TH.Q TH.Type
mkTypeFromRepr repr = case repr of
  WI.BaseBoolRepr -> [t| WI.BaseBoolType |]
  WI.BaseIntegerRepr -> [t| WI.BaseIntegerType |]
  WI.BaseBVRepr nr -> [t| WI.BaseBVType $(return (TH.LitT (TH.NumTyLit (NR.intValue nr)))) |]
  WI.BaseArrayRepr idx ret -> [t| WI.BaseArrayType $(mkTypeFromReprs idx) $(mkTypeFromRepr ret) |]
  WI.BaseStructRepr reprs -> [t| WI.BaseStructType $(mkTypeFromReprs reprs) |]
  _ -> fail $ "mkTypeFromRepr: unsupported type: " ++ show repr

mkTypeFromReprs :: Ctx.Assignment WI.BaseTypeRepr ctx -> TH.Q TH.Type
mkTypeFromReprs reprs = case Ctx.viewAssign reprs of
  Ctx.AssignEmpty -> [t| Ctx.EmptyCtx |]
  Ctx.AssignExtend reprs' repr -> [t| $(mkTypeFromReprs reprs') Ctx.::> $(mkTypeFromRepr repr) |]

-- mkExprFromRepr :: WI.BaseTypeRepr tp -> TH.Q TH.Exp
-- mkExprFromRepr repr = case repr of
--   WI.BaseBoolRepr -> [e| WI.BaseBoolRepr |]
--   WI.BaseIntegerRepr -> [e| WI.BaseIntegerRepr |]
--   WI.BaseBVRepr nr -> do
--     knownNatE <- [e| NR.knownNat |]
--     [e| WI.BaseBVRepr $(return (TH.AppTypeE knownNatE (TH.LitT (TH.NumTyLit (NR.intValue nr))))) |]
--   WI.BaseArrayRepr idx ret -> [e| WI.BaseArrayRepr $(mkExprFromReprs idx) $(mkExprFromRepr ret) |]
--   WI.BaseStructRepr reprs -> [e| WI.BaseStructRepr $(mkExprFromReprs reprs) |]

-- mkExprFromReprs :: Ctx.Assignment WI.BaseTypeRepr ctx -> TH.Q TH.Exp
-- mkExprFromReprs reprs = case Ctx.viewAssign reprs of
--   Ctx.AssignEmpty -> [e| Ctx.empty |]
--   Ctx.AssignExtend reprs' repr -> [e| $(mkExprFromReprs reprs') Ctx.:> $(mkExprFromRepr repr) |]



-- mkReprFromGlobals :: Some (Ctx.Assignment Global) -> TH.Q TH.Exp
-- mkReprFromGlobals (Some globals) = mkExprFromReprs $ FC.fmapFC gbType globals

-- | If a type appears exactly once in the given known context, we can compute its index.

class KnownIndex ctx tp where
  knownIndex :: Ctx.Index ctx tp

instance DistinctIn ctx tp => KnownIndex ctx tp where
  knownIndex = distinctInIndex

type DistinctCtx ctx = ForallCtx (DistinctIn ctx) ctx

withKnownIndex :: forall ctx tp f
                . DistinctCtx ctx
               => Ctx.Index ctx tp
               -> (KnownIndex ctx tp => f)
               -> f
withKnownIndex idx f = withForallCtx (Proxy @(DistinctIn ctx)) idx f

class NeqT a b where
  _neq :: NeqTRepr a b

data NeqTRepr a b where
  NeqTRepr :: ((a == b) ~ 'False) => NeqTRepr a b

instance ((a == b) ~ 'False) => NeqT a b where
  _neq = NeqTRepr

-- | Proof that the given type is not present in the context.
data NotMemberOfProof ctx s where
  NotMemberEmpty :: NotMemberOfProof Ctx.EmptyCtx s
  NotMemberCons :: forall ctx s s'
                 . NeqT s s'
                => NotMemberOfProof ctx s'
                -> NotMemberOfProof (ctx Ctx.::> s) s'

class NotMemberOf ctx s where
  notMemberOfProof :: NotMemberOfProof ctx s
  notMemberOfSize :: Proxy s -> Ctx.Size ctx

instance NotMemberOf Ctx.EmptyCtx s where
  notMemberOfProof = NotMemberEmpty
  notMemberOfSize _ = Ctx.zeroSize

instance (NeqT s s', NotMemberOf ctx s') => NotMemberOf (ctx Ctx.::> s) s' where
  notMemberOfProof = NotMemberCons notMemberOfProof
  notMemberOfSize s = Ctx.incSize (notMemberOfSize s)

-- | Proof that the given type is in the context exactly once
data DistinctInProof ctx tp where
  DistinctInHere :: NotMemberOfProof ctx tp -> DistinctInProof (ctx Ctx.::> tp) tp
  DistinctInThere :: forall ctx tp tp'
                   . NeqT tp' tp
                  => DistinctInProof ctx tp
                  -> DistinctInProof (ctx Ctx.::> tp') tp

class DistinctIn ctx tp where
  distinctInProof :: DistinctInProof ctx tp
  distinctInIndex :: Ctx.Index ctx tp

instance  NotMemberOf ctx tp => DistinctIn (ctx Ctx.::> tp) tp where
  distinctInProof = DistinctInHere notMemberOfProof
  distinctInIndex = Ctx.nextIndex $ notMemberOfSize (Proxy @tp)

instance (NeqT tp' tp, DistinctIn ctx tp) => DistinctIn (ctx Ctx.::> tp') tp where
  distinctInProof = DistinctInThere distinctInProof
  distinctInIndex = Ctx.skipIndex $ distinctInIndex

data CurryC c tp where
  CurryC :: () :- c tp -> CurryC c tp

class ForallCtx c ctx where
  forallCtxProof :: Ctx.Assignment (CurryC c) ctx

instance ForallCtx c Ctx.EmptyCtx where
  forallCtxProof = Ctx.empty

instance (c tp, ForallCtx c ctx) => ForallCtx c (ctx Ctx.::> tp) where
  forallCtxProof = forallCtxProof :> (CurryC (Sub Dict))

forallCtxSize :: forall c ctx
               . ForallCtx c ctx
              => Proxy c
              -> Ctx.Size ctx
forallCtxSize _ = Ctx.size (forallCtxProof :: Ctx.Assignment (CurryC c) ctx)

withForallCtx :: forall c ctx tp f
               . ForallCtx c ctx
              => Proxy c
              -> Ctx.Index ctx tp
              -> (c tp => f)
              -> f
withForallCtx _ idx f =
  let
     CurryC witness = (forallCtxProof :: Ctx.Assignment (CurryC c) ctx) Ctx.! idx
   in f \\ witness

mapForallCtx :: forall ctx c f g
              . ForallCtx c ctx
             => Proxy c
             -> (forall tp. c tp => f tp -> g tp)
             -> Ctx.Assignment f ctx
             -> Ctx.Assignment g ctx
mapForallCtx c f asn = runIdentity $ traverseForallCtx c (\a -> return $ f a) asn


traverseForallCtx :: forall ctx c f g m
              . ForallCtx c ctx
             => Applicative m
             => Proxy c
             -> (forall tp. c tp => f tp -> m (g tp))
             -> Ctx.Assignment f ctx
             -> m (Ctx.Assignment g ctx)
traverseForallCtx c f asn = Ctx.traverseWithIndex (\idx a -> withForallCtx c idx $ f a) asn

forallUpTo :: forall c n maxn
            . ForallCtx c (CtxUpTo maxn)
           => Proxy c
           -> Proxy maxn
           -> NR.NatRepr n
           -> (n <= maxn) :- c n
forallUpTo c _ n = Sub $
  withForallCtx c (natUpToIndex (Proxy @maxn) (forallCtxSize c) n) $
  Dict
