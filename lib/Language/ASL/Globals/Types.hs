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

module Language.ASL.Globals.Types
  ( Global(..)
  , GlobalDomain(..)
  , SGlobal(..)
  , GlobalsType
  , IndexedSymbol
  , IsGlobal
  , IsSimpleGlobal
  , domainSingleton
  , domainUnbounded
  , asSingleton
  , mkInstDeclsFromGlobals
  , mkSimpleInstDecls
  , mkAllGlobalSymsT
  , mkAllGlobalSymsE
  , mkTypeFromGlobals
  , mkTypeFromReprs
  , mkReprFromGlobals
  , mapNatsUpto
  , mkNatCtx
  , genCond
  , liftIndex
  , liftIndexNatRepr
  , liftIndexNumT
  , mkGlobalsT
  , mkGlobalsE
  , mkSymbolE
  , mkSymbolT
  ) where

import           GHC.Natural ( naturalFromInteger )
import           GHC.TypeLits

import           Control.Applicative ( Const(..) )
import           Control.Monad ( forM, foldM )
import           Control.Monad.Except ( throwError )
import qualified Control.Monad.Except as ME

import           GHC.TypeNats ( KnownNat )
import           Data.Parameterized.Some ( Some(..), viewSome )
import           Data.Parameterized.Ctx ( type (<+>) )
import           Data.Parameterized.Context ( EmptyCtx, (::>), Assignment, empty, pattern (:>) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Map ( MapF )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair

import           Data.Maybe ( catMaybes )
import           Data.List ( intercalate )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Text as T
import           Data.Parameterized.NatRepr ( type (<=) )
import           Data.Parameterized.Classes
import qualified What4.Interface as WI
import qualified What4.Concrete as WI

import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT

import           Language.ASL.Signature
import           Language.ASL.Types

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH


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
    , gbGroupName :: Maybe T.Text
    -- ^ Either "SIMD" or "GPR". This global will be accessed via this name plus an index.
    }

instance TestEquality Global where
  testEquality (Global nm tp dm gn) (Global nm' tp' dm' gn') =
    case testEquality tp tp' of
      Just Refl | nm == nm' && dm == dm' && gn == gn' -> Just Refl
      _ -> Nothing

data GlobalDomain tp =
    DomainSet (Set (WI.ConcreteVal tp))
    -- ^ the global is one of a fixed set of values
  | DomainSpan (Maybe (WI.ConcreteVal tp)) (Maybe (WI.ConcreteVal tp))
    -- ^ the global is in a range of values (inclusive). A 'Nothing' bound indicates
    -- it is unbounded in that direction.
  | DomainUndefined
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

mapSpan :: (WI.ConcreteVal tp -> a)
        -> (Maybe (WI.ConcreteVal tp), Maybe (WI.ConcreteVal tp))
        -> (Maybe a, Maybe a)
mapSpan f (v1, v2) = (fmap f v1, fmap f v2)


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
      go v pred =
        let
          e' = concreteToExpr v
          isEq = CCG.App $ CCE.BaseIsEq (WI.concreteType v) e e'
        in mkOr isEq pred
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

globalSymbol :: Global tp -> WI.SolverSymbol
globalSymbol gb = WI.safeSymbol (T.unpack (gbName gb))

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
      Nothing -> ME.throwError $ "Missing global specification for: "
        ++ T.unpack (projectLabel lblv) ++ " " ++ show (projectValue lblv)


genCond :: forall ext s ctx err m
         . (Monad m, ME.MonadError err m)
        => (String -> err)
        -> Map T.Text (Some Global)
        -> (forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> m (CCG.Expr ext s (CT.BaseToType tp)))
        -> Ctx.Assignment (LabeledValue T.Text WI.BaseTypeRepr) ctx
        -> m [(T.Text, CCG.Expr ext s CT.BoolType)]
genCond mkerr globalsMap lookup sig = do
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
      expr <- lookup lblv
      return $ Const $ (projectLabel lblv, domainPred gb expr)

-- Retrieving indexes into the globals based on type-level symbols

type family GlobalsType (s :: Symbol) :: WI.BaseType
type family IndexedSymbol (s :: Symbol) (n :: Nat) :: Symbol


class KnownSymbol s => IsSimpleGlobal (s:: Symbol) where
  hasKnownGlobalReprSimple :: CT.SymbolRepr s -> WI.BaseTypeRepr (GlobalsType s)

class KnownSymbol s => IsGlobal (s:: Symbol) where
  hasKnownGlobalRepr :: CT.SymbolRepr s -> WI.BaseTypeRepr (GlobalsType s)

class HasIndexedSymbol (s :: Symbol) (n :: Nat) where
  hasIndexedSymbol :: CT.SymbolRepr s -> NR.NatRepr n -> CT.SymbolRepr (IndexedSymbol s n)


--class (KnownSymbol s, KnownNat n) => IsIndexedSymbol (s :: Symbol) (n :: Nat) where
--  hasKnownIndexedSymbol :: CT.SymbolRepr s -> NR.NatRepr n -> CT.SymbolRepr (IndexedSymbol s n)

data SGlobal ctx (s :: Symbol) where
  SGlobal :: { unSG :: Ctx.Index ctx (GlobalsType s) } -> SGlobal ctx s

symToSGlobal :: forall s ctx. MapF (LabeledValue T.Text WI.BaseTypeRepr) (Ctx.Index ctx)
          -> CT.SymbolRepr s
          -> WI.BaseTypeRepr (GlobalsType s)
          -> SGlobal ctx s
symToSGlobal f srepr trepr = case MapF.lookup (LabeledValue (CT.symbolRepr srepr) trepr) f of
  Just idx -> SGlobal idx
  Nothing -> error $ "No corresponding global for: " ++ show srepr

mkGlobalsGen :: forall a
              . (a -> a -> TH.Q a)
             -> TH.Q a
             -> Some (Ctx.Assignment Global)
             -> (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q a)
             -> TH.Q a
mkGlobalsGen comb mkinit (Some gbs) mkelem = do
  elems <- Ctx.traverseWithIndex go gbs
  init <- mkinit
  FC.foldlMFC (\b (Const a) -> comb b a) init elems
  where
    go :: Ctx.Index ctx tp -> Global tp -> TH.Q (Const a tp)
    go idx gb = Const <$> mkelem idx gb

mkGlobalsE :: Some (Ctx.Assignment Global)
           -> (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q TH.Exp)
           -> TH.Q TH.Exp
mkGlobalsE = mkGlobalsGen (\b a -> [e| $(return b) Ctx.:> $(return a) |]) [e| Ctx.empty |]

mkGlobalsT :: Some (Ctx.Assignment Global)
           -> (forall (ctx :: Ctx.Ctx WI.BaseType) (tp :: WI.BaseType). Ctx.Index ctx tp -> Global tp -> TH.Q TH.Type)
           -> TH.Q TH.Type
mkGlobalsT = mkGlobalsGen (\b a -> [t| $(return b) Ctx.::> $(return a) |]) [t| Ctx.EmptyCtx |]

-- | T.Text -> [t| Symbol |]
mkSymbolT :: T.Text -> TH.Q TH.Type
mkSymbolT nm = TH.litT (TH.strTyLit (T.unpack $ nm))

-- | T.Text -> [e| CT.SymbolRepr |]
mkSymbolE :: T.Text -> TH.Q TH.Exp
mkSymbolE nm = [e| CT.knownSymbol :: CT.SymbolRepr $(mkSymbolT nm) |]

mkInstDeclsFromGlobals :: Some (Ctx.Assignment Global) -> TH.DecsQ
mkInstDeclsFromGlobals gbs = mkGlobalsGen (\b a -> return $ b ++ a) (return []) gbs go
 where
   go :: Ctx.Index ctx tp -> Global tp -> TH.DecsQ
   go idx gb = do
     symbT <- mkSymbolT (gbName gb)
     decls <- [d|
      type instance GlobalsType $(return symbT) = $(mkTypeFromRepr (gbType gb))
      instance IsGlobal $(return symbT) where
        hasKnownGlobalRepr _ = $(mkExprFromRepr (gbType gb))
      |]
     decls' <- case gbGroupName gb of
       Just grpNm ->
         [d|
           type instance IndexedSymbol $(mkSymbolT grpNm) $(liftIndexNumT idx) = $(return symbT)
         |]
       Nothing -> return []
     return $ decls ++ decls'

mkSimpleInstDecls :: Some (Ctx.Assignment Global) -> TH.DecsQ
mkSimpleInstDecls gbs = mkGlobalsGen (\b a -> return $ b ++ a) (return []) gbs go
  where
    go :: Ctx.Index ctx tp -> Global tp -> TH.DecsQ
    go _idx gb = [d| instance IsSimpleGlobal $(mkSymbolT (gbName gb)) |]

-- | withNatsUpto :: maxnat -> (f :: (\nr -> *)) -> [ f (NatRepr n) | n <- forall n. n <= maxnat ]
mapNatsUpto :: Integer -> TH.Q TH.Exp -> TH.Q TH.Exp
mapNatsUpto maxnr f = go maxnr
  where
    go :: Integer -> TH.Q TH.Exp
    go i | i < 0 = [e| [] |]
    go i = [e| $(f) (NR.knownNat :: NR.NatRepr $(TH.litT (TH.numTyLit i))) : $(go (i - 1)) |]

-- | mkNatCtx :: maxnat -> EmptyCtx ::> 0 ::> 1 ... ::> maxnat
mkNatCtx :: Integer -> TH.Q TH.Type
mkNatCtx maxnr = go maxnr
  where
    go :: Integer -> TH.Q TH.Type
    go i | i < 0 = [t| Ctx.EmptyCtx |]
    go i = [t| $(go (i-1)) Ctx.::> $(TH.litT (TH.numTyLit i)) |]

mkAllGlobalSymsT :: Some (Ctx.Assignment Global) -> TH.Q TH.Type
mkAllGlobalSymsT gbs = mkGlobalsT gbs $ \_ gb -> mkSymbolT (gbName gb)

mkAllGlobalSymsE :: Some (Ctx.Assignment Global) -> TH.Q TH.Exp
mkAllGlobalSymsE gbs = mkGlobalsE gbs $ \_ gb -> mkSymbolE (gbName gb)

liftIndex :: Ctx.Index ctx tp -> TH.Q TH.Exp
liftIndex idx = [e| Ctx.natIndexProxy $(liftIndexNatRepr idx) |]

liftIndexNatRepr :: Ctx.Index ctx tp -> TH.Q TH.Exp
liftIndexNatRepr idx = [e| NR.knownNat :: NR.NatRepr $(liftIndexNumT idx) |]

liftIndexNumT :: Ctx.Index ctx tp -> TH.Q TH.Type
liftIndexNumT idx = TH.litT (TH.numTyLit(fromIntegral $ Ctx.indexVal idx))

mkTypeFromRepr :: WI.BaseTypeRepr tp -> TH.Q TH.Type
mkTypeFromRepr repr = case repr of
  WI.BaseBoolRepr -> [t| WI.BaseBoolType |]
  WI.BaseIntegerRepr -> [t| WI.BaseIntegerType |]
  WI.BaseBVRepr nr -> [t| WI.BaseBVType $(return (TH.LitT (TH.NumTyLit (NR.intValue nr)))) |]
  WI.BaseArrayRepr idx ret -> [t| WI.BaseArrayType $(mkTypeFromReprs idx) $(mkTypeFromRepr ret) |]
  WI.BaseStructRepr reprs -> [t| WI.BaseStructType $(mkTypeFromReprs reprs) |]

mkTypeFromReprs :: Ctx.Assignment WI.BaseTypeRepr ctx -> TH.Q TH.Type
mkTypeFromReprs reprs = case Ctx.viewAssign reprs of
  Ctx.AssignEmpty -> [t| Ctx.EmptyCtx |]
  Ctx.AssignExtend reprs' repr -> [t| $(mkTypeFromReprs reprs') Ctx.::> $(mkTypeFromRepr repr) |]

mkExprFromRepr :: WI.BaseTypeRepr tp -> TH.Q TH.Exp
mkExprFromRepr repr = case repr of
  WI.BaseBoolRepr -> [e| WI.BaseBoolRepr |]
  WI.BaseIntegerRepr -> [e| WI.BaseIntegerRepr |]
  WI.BaseBVRepr nr -> do
    knownNatE <- [e| NR.knownNat |]
    [e| WI.BaseBVRepr $(return (TH.AppTypeE knownNatE (TH.LitT (TH.NumTyLit (NR.intValue nr))))) |]
  WI.BaseArrayRepr idx ret -> [e| WI.BaseArrayRepr $(mkExprFromReprs idx) $(mkExprFromRepr ret) |]
  WI.BaseStructRepr reprs -> [e| WI.BaseStructRepr $(mkExprFromReprs reprs) |]

mkExprFromReprs :: Ctx.Assignment WI.BaseTypeRepr ctx -> TH.Q TH.Exp
mkExprFromReprs reprs = case Ctx.viewAssign reprs of
  Ctx.AssignEmpty -> [e| Ctx.empty |]
  Ctx.AssignExtend reprs' repr -> [e| $(mkExprFromReprs reprs') Ctx.:> $(mkExprFromRepr repr) |]

mkTypeFromGlobals :: Some (Ctx.Assignment Global) -> TH.Q TH.Type
mkTypeFromGlobals (Some globals) = mkTypeFromReprs $ FC.fmapFC gbType globals

mkReprFromGlobals :: Some (Ctx.Assignment Global) -> TH.Q TH.Exp
mkReprFromGlobals (Some globals) = mkExprFromReprs $ FC.fmapFC gbType globals
