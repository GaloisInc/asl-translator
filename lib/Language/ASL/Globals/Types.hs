{-# LANGUAGE GADTs #-}
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


module Language.ASL.Globals.Types
  ( Global(..)
  , GlobalDomain(..)
  , SGlobal(..)
  , GlobalsType
  , IsGlobal
  , domainSingleton
  , domainUnbounded
  , asSingleton
  , mkInstDeclsFromGlobals
  , mkAllGlobalSymsT
  , mkGlobalsSyms
  , mkTypeFromGlobals
  , mkTypeFromReprs
  , mkReprFromGlobals
  , foldGlobals
  , genCond
  ) where

import           GHC.Natural ( naturalFromInteger )
import           GHC.TypeLits

import           Control.Applicative ( Const(..) )
import           Control.Monad ( forM, foldM )
import           Control.Monad.Except ( throwError )
import qualified Control.Monad.Except as ME

import           GHC.TypeNats ( KnownNat )
import           Data.Parameterized.Some ( Some(..) )
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
    -- ^ The known domain of this global variable.
    --
    -- Every update to this value needs to check that this domain has been respected.
    }

data GlobalDomain tp =
    DomainSet (Set (WI.ConcreteVal tp))
    -- ^ the global is one of a fixed set of values
  | DomainSpan (Maybe (WI.ConcreteVal tp)) (Maybe (WI.ConcreteVal tp))
    -- ^ the global is in a range of values (inclusive). A 'Nothing' bound indicates
    -- it is unbounded in that direction.
  | DomainUndefined

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

class KnownSymbol s => IsGlobal (s:: Symbol) where
  hasKnownGlobalRepr :: CT.SymbolRepr s -> WI.BaseTypeRepr (GlobalsType s)

data SGlobal ctx (s :: Symbol) where
  SGlobal :: { unSG :: Ctx.Index ctx (GlobalsType s) } -> SGlobal ctx s

symToSGlobal :: forall s ctx. MapF (LabeledValue T.Text WI.BaseTypeRepr) (Ctx.Index ctx)
          -> CT.SymbolRepr s
          -> WI.BaseTypeRepr (GlobalsType s)
          -> SGlobal ctx s
symToSGlobal f srepr trepr = case MapF.lookup (LabeledValue (CT.symbolRepr srepr) trepr) f of
  Just idx -> SGlobal idx
  Nothing -> error $ "No corresponding global for: " ++ show srepr


data ReifiedGlobal = ReifiedGlobal
   { symbolT :: TH.Type
   , symbolE :: TH.Exp
   , typeT :: TH.Type
   , typeE :: TH.Exp
   }

mapAllGlobals :: forall a
               . (ReifiedGlobal -> TH.Q a)
              -> (a -> a -> TH.Q a)
              -> TH.Q a
              -> Some (Ctx.Assignment Global)
              -> TH.Q a
mapAllGlobals mkelem comb fin (Some globals) = go globals
  where
    go :: Ctx.Assignment Global ctx -> TH.Q a
    go globals' = case Ctx.viewAssign globals' of
      Ctx.AssignEmpty -> fin
      Ctx.AssignExtend asn' gb -> do
        rest <- go asn'
        symbolT' <- TH.litT (TH.strTyLit (T.unpack $ gbName gb))
        symbolE' <- [e| CT.knownSymbol :: CT.SymbolRepr $(return symbolT') |]
        typeT' <- mkTypeFromRepr (gbType gb)
        typeE' <- mkExprFromRepr (gbType gb)
        elem <- mkelem (ReifiedGlobal symbolT' symbolE' typeT' typeE')
        comb elem rest


mkInstDeclsFromGlobals :: Some (Ctx.Assignment Global) -> TH.DecsQ
mkInstDeclsFromGlobals = mapAllGlobals go (\d1 d2 -> return $ d1 ++ d2) (return [])
 where
   go :: ReifiedGlobal -> TH.Q [TH.Dec]
   go (ReifiedGlobal sT sE tT tE) = [d|
      type instance GlobalsType $(return sT) = $(return tT)
      instance IsGlobal $(return sT) where
        hasKnownGlobalRepr _ = $(return tE)
      |]

mkAllGlobalSymsT :: Some (Ctx.Assignment Global) -> TH.Q TH.Type
mkAllGlobalSymsT = mapAllGlobals go (\t1 t2 -> [t| $(return t2) Ctx.::> $(return t1) |]) [t| Ctx.EmptyCtx |]
  where
    go :: ReifiedGlobal -> TH.Q TH.Type
    go (ReifiedGlobal sT sE tT tE) = return sT

foldGlobals :: Some (Ctx.Assignment Global) -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp -> TH.Q TH.Exp
foldGlobals glbs mkelem combElem init =
    mapAllGlobals go (\e1 e2 -> [e| $(combElem) $(return e2) $(return e1) |]) [e| $(init) |] glbs
  where
    go :: ReifiedGlobal -> TH.Q TH.Exp
    go (ReifiedGlobal sT sE tT tE) =
      [e| $(mkelem) $(return sE) $(return tE) |]

mkGlobalsSyms :: Some (Ctx.Assignment Global) -> TH.Q TH.Exp
mkGlobalsSyms glbs = do
  vargbl <- TH.newName "varglbs"
  TH.lamE [TH.varP vargbl] (mapAllGlobals (go (TH.VarE vargbl)) (\e1 e2 -> [e| $(return e1) : $(return e2) |]) [e| [] |] glbs)
  where
    go :: TH.Exp -> ReifiedGlobal -> TH.Q TH.Exp
    go glbsE (ReifiedGlobal sT sE tT tE) =
      [e| Pair $(return sE) (symToSGlobal $(return glbsE) $(return sE) $(return tE)) |]

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
