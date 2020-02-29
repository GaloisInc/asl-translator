{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.ASL.Globals
  ( trackedGlobals
  , untrackedGlobals
  , untrackedGlobalReprs
  , trackedGlobalReprs
  , trackedGlobalBaseReprs
  , GlobalsCtx
  , UntrackedGlobalsCtx
  , getPrecond
  , getPostcond
  , globalsMap
  , staticGlobals
  , getGlobalsSubMap
  , lookupGlobal
  , Global(..)
  , GlobalsType
  , IndexedSymbol
  , GlobalRef(..)
  , SimpleGlobalRef
  , GPRRef
  , SIMDRef
  , simpleGlobalRefs
  , gprGlobalRefs
  , simdGlobalRefs
  , memoryGlobalRef
  , allGlobalRefs
  , GlobalSymsCtx
  , lookupGlobalRef
  , knownIndexedGlobalRef
  , knownGlobalRef
  , mkGPRRef
  , mkGPRGlobalRef
  , mkSIMDRef
  , mkSIMDGlobalRef
  , mkSimpleGlobalRef
  , globalRefSymbol
  , globalRefRepr
  , testGlobalEq
  , resolveGlobalRef
  , withGPRRepr
  , withSIMDRepr
  )

where

import           GHC.TypeLits

import           Control.Applicative ( Const(..) )
import           Control.Monad.Identity
import qualified Control.Monad.Except as ME

import qualified Data.Text as T
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes, fromJust )


import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Map ( MapF )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair

import qualified What4.Interface as WI
import qualified What4.Concrete as WI

import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT

import           Language.ASL.StaticExpr
import           Language.ASL.Signature
import           Language.ASL.Types

import           Language.ASL.Globals.Types
import           Language.ASL.Globals.Definitions

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

type UntrackedGlobalsCtx = $(mkTypeFromGlobals untrackedGlobals')
type SimpleGlobalsCtx = $(mkTypeFromGlobals simpleGlobals')

type GPRCtx = $(mkTypeFromGlobals gprGlobals')
type SIMDCtx = $(mkTypeFromGlobals simdGlobals')

type GlobalsCtx = $(mkTypeFromGlobals trackedGlobals')

simpleEmbedding :: CtxEmbedding SimpleGlobalsCtx GlobalsCtx
simpleEmbedding =
  extendEmbeddingRight $ extendEmbeddingRight $ extendEmbeddingRight $ identityEmbedding (Ctx.size simpleGlobals)

untrackedGlobalBaseReprs :: Assignment WI.BaseTypeRepr UntrackedGlobalsCtx
untrackedGlobalBaseReprs = $(mkReprFromGlobals untrackedGlobals')

trackedGlobalBaseReprs :: Assignment WI.BaseTypeRepr GlobalsCtx
trackedGlobalBaseReprs = $(mkReprFromGlobals trackedGlobals')

untrackedGlobals :: Assignment Global UntrackedGlobalsCtx
untrackedGlobals = case untrackedGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) untrackedGlobalBaseReprs -> gbs
  _ -> error "template haskell error"

untrackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) UntrackedGlobalsCtx
untrackedGlobalReprs = FC.fmapFC (\gb -> LabeledValue (gbName gb) (gbType gb)) untrackedGlobals

trackedGlobals :: Assignment Global GlobalsCtx
trackedGlobals = case trackedGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) trackedGlobalBaseReprs -> gbs
  _ -> error "template haskell error"

simpleGlobalBaseReprs :: Assignment WI.BaseTypeRepr SimpleGlobalsCtx
simpleGlobalBaseReprs = $(mkReprFromGlobals simpleGlobals')

simpleGlobals :: Assignment Global SimpleGlobalsCtx
simpleGlobals = case simpleGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) simpleGlobalBaseReprs -> gbs
  _ -> error "template haskell error"

gprGlobalBaseReprs :: Assignment WI.BaseTypeRepr GPRCtx
gprGlobalBaseReprs = $(mkReprFromGlobals gprGlobals')

gprGlobals :: Assignment Global GPRCtx
gprGlobals = case gprGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) gprGlobalBaseReprs -> gbs
  _ -> error "template haskell error"

simdGlobalBaseReprs :: Assignment WI.BaseTypeRepr SIMDCtx
simdGlobalBaseReprs = $(mkReprFromGlobals simdGlobals')

simdGlobals :: Assignment Global SIMDCtx
simdGlobals = case gprGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) simdGlobalBaseReprs -> gbs
  _ -> error "template haskell error"

trackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) GlobalsCtx
trackedGlobalReprs = FC.fmapFC (\gb -> LabeledValue (gbName gb) (gbType gb)) trackedGlobals

getPrecond :: forall ext s reads writes args ret err m
            . (Monad m, ME.MonadError err m)
           => (String -> err)
           -> (forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> m (CCG.Expr ext s (CT.BaseToType tp)))
           -> FunctionSignature reads writes args ret
           -> m [(T.Text, CCG.Expr ext s CT.BoolType)]
getPrecond mkerr lookup' sig = genCond mkerr globalsMap lookup' (funcGlobalReadReprs sig)

getPostcond :: forall ext s reads writes args ret err m
             . (Monad m, ME.MonadError err m)
            => (String -> err)
            -> (forall tp. LabeledValue T.Text WI.BaseTypeRepr tp -> m (CCG.Expr ext s (CT.BaseToType tp)))
            -> FunctionSignature reads writes args ret
            -> m [(T.Text, CCG.Expr ext s CT.BoolType)]
getPostcond mkerr lookup' sig = genCond mkerr globalsMap lookup' (funcGlobalWriteReprs sig)

globalsMap :: Map T.Text (Some Global)
globalsMap = Map.fromList $
  map (\(Some gb) -> (gbName gb, Some gb)) $
    (FC.toListFC Some trackedGlobals ++ FC.toListFC Some untrackedGlobals)

mkMapIndexF :: forall globals
             . Assignment Global globals
            -> MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index globals)
mkMapIndexF reprs = runIdentity $ do
  pairs <- traverseWithIndex mkEntry reprs
  return $ MapF.fromList $ FC.toListFC (\(Const c) -> c) pairs
  where
    mkEntry :: Index globals tp
            -> Global tp
            -> Identity (Const (Pair (LabeledValue T.Text WI.BaseTypeRepr) (Index globals)) tp)
    mkEntry idx gb = return $ Const $ Pair (LabeledValue (gbName gb) (gbType gb)) idx

globalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index GlobalsCtx)
globalsMapIndexF = mkMapIndexF trackedGlobals

untrackedGlobalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index UntrackedGlobalsCtx)
untrackedGlobalsMapIndexF = mkMapIndexF untrackedGlobals

lookupUntrackedGlobal :: LabeledValue T.Text WI.BaseTypeRepr tp -> Maybe (Global tp)
lookupUntrackedGlobal lbl = (\idx -> untrackedGlobals ! idx) <$> MapF.lookup lbl untrackedGlobalsMapIndexF

lookupTrackedGlobal :: LabeledValue T.Text WI.BaseTypeRepr tp -> Maybe (Global tp)
lookupTrackedGlobal lbl = (\idx -> trackedGlobals ! idx) <$> MapF.lookup lbl globalsMapIndexF

lookupGlobal :: LabeledValue T.Text WI.BaseTypeRepr tp -> Maybe (Either (Global tp) (Global tp))
lookupGlobal lbl = case (lookupUntrackedGlobal lbl, lookupTrackedGlobal lbl) of
  (Just uglb, Nothing) -> Just $ Left uglb
  (Nothing, Just tglb) -> Just $ Right tglb
  (Nothing, Nothing) -> Nothing
  _ -> error $ "Duplicate global: " ++ show lbl

concreteToStatic :: WI.ConcreteVal tp -> Maybe StaticValue
concreteToStatic cv = case cv of
  WI.ConcreteBool b -> Just $ StaticBool b
  WI.ConcreteInteger i -> Just $ StaticInt i
  WI.ConcreteBV nr bv -> Just $ StaticBV $ integerToBits (WI.intValue nr) bv
  _ -> Nothing

staticGlobals :: StaticValues
staticGlobals = Map.mapMaybe getStaticGlobal globalsMap
  where
    getStaticGlobal :: Some Global -> Maybe StaticValue
    getStaticGlobal (Some gb) = do
      cv <- asSingleton (gbDomain gb)
      concreteToStatic cv



getGlobalsSubMap :: forall m ctx
                  . (Monad m, ME.MonadError String m)
                 => Assignment (LabeledValue T.Text WI.BaseTypeRepr) ctx
                 -> m (MapF (Index GlobalsCtx) (Index ctx))
getGlobalsSubMap reprs = do
  pairs <- traverseWithIndex mkEntry reprs
  return $ MapF.fromList $ catMaybes $ FC.toListFC (\(Const c) -> c) pairs
  where
    mkEntry :: Index ctx tp -> LabeledValue T.Text WI.BaseTypeRepr tp -> m (Const (Maybe (Pair (Index GlobalsCtx) (Index ctx))) tp)
    mkEntry idx lblv = case MapF.lookup lblv globalsMapIndexF of
      Just idx' -> return $ Const $ Just $ Pair idx' idx
      Nothing -> case MapF.lookup lblv untrackedGlobalsMapIndexF of
        Just _ -> return $ Const $ Nothing
        Nothing -> ME.throwError $ "Missing global specification for: " ++ show lblv

$(mkInstDeclsFromGlobals simpleGlobals')
$(mkInstDeclsFromGlobals gprGlobals')
$(mkInstDeclsFromGlobals simdGlobals')
$(mkInstDeclsFromGlobals (forSome memoryGlobal' $ \gb -> Some (empty :> gb)))

type SimpleGlobalSymsCtx = $(mkAllGlobalSymsT simpleGlobals')
type GPRSymsCtx = $(mkAllGlobalSymsT gprGlobals')
type SIMDSymsCtx = $(mkAllGlobalSymsT simdGlobals')

type GlobalSymsCtx = SimpleGlobalSymsCtx <+> GPRSymsCtx <+> SIMDSymsCtx ::> "__Memory"

-- ^ A 'SimpleGlobalRef' is a refernce to a single piece of
-- global state (i.e. a meta-state flag or the processor state).
data SimpleGlobalRef (s :: Symbol) where
  SimpleGlobalRef' :: CT.SymbolRepr s
                   -> Index SimpleGlobalsCtx (GlobalsType s)
                   -> SimpleGlobalRef s

-- | A 'GPRRef' represents a reference to a particular general-purpose register.
data GPRRef (n :: Nat) where
  GPRRef' :: ValidNatRepr GPRCtx n
          -> Index GPRCtx (WI.BaseBVType 32)
          -> GPRRef n

-- | A 'GPRRef' represents a reference to a particular SIMD register.
data SIMDRef (n :: Nat) where
  SIMDRef' :: ValidNatRepr SIMDCtx n
           -> Index SIMDCtx (WI.BaseBVType 128)
           -> SIMDRef n

-- | A 'GlobalRef' refers to any single piece of global state tracked by the ASL semantics.
data GlobalRef (s :: Symbol) where
  SimpleGlobalRef :: SimpleGlobalRef s -> GlobalRef s
  GPRRef :: GPRRef n -> GlobalRef (IndexedSymbol "GPRS" n)
  SIMDRef :: SIMDRef n -> GlobalRef (IndexedSymbol "SIMD" n)
  MemoryRef :: Index GlobalsCtx (GlobalsType "__Memory") -> GlobalRef "__Memory"
  -- ^ The distinguished global state variable representing memory.

simpleGlobalRefs :: Assignment GlobalRef SimpleGlobalSymsCtx
simpleGlobalRefs = $(mkGlobalAssignment simpleGlobals'
    (\idx -> [e| \symb _ -> SimpleGlobalRef (SimpleGlobalRef' symb $(liftIndex idx)) |]))

gprGlobalRefs :: Assignment GlobalRef GPRSymsCtx
gprGlobalRefs =
  $(let mkGPRRefE:: Index ctx tp -> TH.Q TH.Exp
        mkGPRRefE idx =
          [e| \_ _ ->
              let ref :: GPRRef $(liftIndexNumT idx)
                  ref = GPRRef' (ValidNatRepr $(liftIndexNatRepr idx)) $(liftIndex idx)
              in GPRRef ref |]
    in mkGlobalAssignment gprGlobals' mkGPRRefE)

simdGlobalRefs :: Assignment GlobalRef SIMDSymsCtx
simdGlobalRefs =
  $(let mkSIMDRefE :: Index ctx tp -> TH.Q TH.Exp
        mkSIMDRefE idx =
          [e| \_ _ ->
              let
                ref :: SIMDRef $(liftIndexNumT idx)
                ref = SIMDRef' (ValidNatRepr $(liftIndexNatRepr idx)) $(liftIndex idx)
              in SIMDRef ref |]
      in mkGlobalAssignment simdGlobals' mkSIMDRefE)


memoryGlobalIdx :: Index GlobalsCtx (GlobalsType "__Memory")
memoryGlobalIdx = lastIndex $ (Ctx.size trackedGlobals)

memoryGlobalRef :: GlobalRef "__Memory"
memoryGlobalRef = MemoryRef memoryGlobalIdx

allGlobalRefs :: Assignment GlobalRef GlobalSymsCtx
allGlobalRefs = simpleGlobalRefs <++> gprGlobalRefs <++> simdGlobalRefs :> memoryGlobalRef

globalRefMap :: MapF CT.SymbolRepr GlobalRef
globalRefMap = MapF.fromList $
  FC.toListFC (\gb -> Pair (globalRefSymbol gb) gb) allGlobalRefs

gprTypePrf :: ValidNatRepr GPRCtx n
           -> GlobalsType (IndexedSymbol "GPRS" n) :~: WI.BaseBVType 32
gprTypePrf (ValidNatRepr nr) = $(forNats 14 [e| Refl |]) nr

simdTypePrf :: ValidNatRepr SIMDCtx n
            -> GlobalsType (IndexedSymbol "SIMD" n) :~: WI.BaseBVType 128
simdTypePrf (ValidNatRepr nr) = $(forNats 31 [e| Refl |]) nr

gprIdxPrf :: Index GPRCtx tp
          -> tp :~: WI.BaseBVType 32
gprIdxPrf idx | Just Refl <- testEquality (gprGlobalBaseReprs ! idx) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 32)) = Refl
gprIdxPrf _ = error "Invalid gprs"

simdIdxPrf :: Index SIMDCtx tp
          -> tp :~: WI.BaseBVType 128
simdIdxPrf idx | Just Refl <- testEquality (simdGlobalBaseReprs ! idx) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 128)) = Refl
simdIdxPrf _ = error "Invalid simds"

data ValidNatRepr (ctx :: Ctx k) (n :: Nat) where
  ValidNatRepr :: forall ctx n. (n+1 <= CtxSize ctx) => NR.NatRepr n -> ValidNatRepr ctx n

withValidNatRepr :: forall ctx n a
                  . Size ctx
                 -> ValidNatRepr ctx n
                 -> (n <= (CtxSize ctx - 1) => NR.NatRepr n -> a)
                 -> a
withValidNatRepr sz (ValidNatRepr nr) f
  | NR.LeqProof <- NR.leqSub2 (NR.leqProof (NR.addNat nr (NR.knownNat @1)) (ctxSizeRepr sz)) (NR.leqRefl (NR.knownNat @1))
  , Refl <- NR.plusMinusCancel nr (NR.knownNat @1)
  = f nr

ctxSizeRepr :: forall ctx. Size ctx -> NR.NatRepr (CtxSize ctx)
ctxSizeRepr sz = case viewSize sz of
  ZeroSize -> NR.knownNat
  IncSize sz' -> NR.addNat (NR.knownNat @1) (ctxSizeRepr sz')

indexToValidNat :: forall ctx tp
                 . Size ctx
                -> Index ctx tp
                -> Some (ValidNatRepr ctx)
indexToValidNat sz idx |
    Just (Some nr) <- NR.someNat (indexVal idx)
  , Just NR.LeqProof <- NR.testLeq (NR.addNat nr (NR.knownNat @1)) (ctxSizeRepr sz)
  = Some $ ValidNatRepr $ nr
indexToValidNat _ _ = error "indexToValidNat: bad index"

validNatToIndex :: forall ctx n
                 . Size ctx
                -> ValidNatRepr ctx n
                -> Some (Index ctx)
validNatToIndex sz (ValidNatRepr nr) = fromJust $ intIndex (fromIntegral $ NR.natValue nr) sz

gprSymbolRepr :: ValidNatRepr GPRCtx n -> CT.SymbolRepr (IndexedSymbol "GPRS" n)
gprSymbolRepr (ValidNatRepr nr) = $(forNats 14 [e| CT.knownSymbol |]) nr

simdSymbolRepr :: ValidNatRepr SIMDCtx n -> CT.SymbolRepr (IndexedSymbol "SIMD" n)
simdSymbolRepr (ValidNatRepr nr) = $(forNats 31 [e| CT.knownSymbol |]) nr

gprGlobalIndex :: Index GlobalsCtx (WI.BaseStructType GPRCtx)
gprGlobalIndex = skipIndex $ skipIndex $ lastIndex $ decSize $ decSize $ (Ctx.size trackedGlobals)

simdGlobalIdx :: Index GlobalsCtx (WI.BaseStructType SIMDCtx)
simdGlobalIdx =  skipIndex $ lastIndex $ decSize $ (Ctx.size trackedGlobals)

-- | Resolve a 'GlobalRef' against a given 'Assignment'. In the case of register globals,
-- the provided function is used to project out the appropriate register.
resolveGlobalRef :: (forall ctx. f (WI.BaseStructType ctx) -> Index ctx (GlobalsType s) -> f (GlobalsType s))
                 -> Assignment f GlobalsCtx
                 -> GlobalRef s
                 -> f (GlobalsType s)
resolveGlobalRef resolveidx asn gr = case gr of
  SimpleGlobalRef (SimpleGlobalRef' _ idx) -> asn ! (applyEmbedding' simpleEmbedding idx)
  GPRRef (GPRRef' vnr idx)
    | Refl <- gprTypePrf vnr -> resolveidx (asn ! gprGlobalIndex) idx
  SIMDRef (SIMDRef' vnr idx)
    | Refl <- simdTypePrf vnr -> resolveidx (asn ! simdGlobalIdx) idx
  MemoryRef idx -> asn ! idx

testGlobalEq :: forall s s'
              . IsGlobal s
             => GlobalRef s'
             -> Maybe (s :~: s')
testGlobalEq gr = do
  Refl <- testEquality (knownGlobalRef @s) gr
  return Refl


globalRefSymbol :: GlobalRef s -> CT.SymbolRepr s
globalRefSymbol gr = case gr of
  SimpleGlobalRef (SimpleGlobalRef' symb _) -> symb
  GPRRef (GPRRef' vnr _) -> gprSymbolRepr vnr
  SIMDRef (SIMDRef' vnr _) -> simdSymbolRepr vnr
  MemoryRef _ -> CT.knownSymbol

globalRefRepr :: GlobalRef s -> WI.BaseTypeRepr (GlobalsType s)
globalRefRepr = resolveGlobalRef (\(WI.BaseStructRepr repr) idx -> repr ! idx) trackedGlobalBaseReprs

-- Here we explicitly assume that each symbol represents a unique global ref
instance TestEquality GlobalRef where
  testEquality gr1 gr2 = case (globalRefSymbol gr1, globalRefSymbol gr2) of
    (s1, s2) -> testEquality s1 s2

instance OrdF GlobalRef where
  compareF gr1 gr2 = case (globalRefSymbol gr1, globalRefSymbol gr2) of
    (s1, s2) -> compareF s1 s2


lookupGlobalRefSym :: CT.SymbolRepr s -> Maybe (GlobalRef s)
lookupGlobalRefSym symb = MapF.lookup symb globalRefMap

lookupGlobalRef :: String -> Maybe (Some GlobalRef)
lookupGlobalRef str = case CT.someSymbol (T.pack str) of
  Some symb -> Some <$> lookupGlobalRefSym symb

knownIndexedGlobalRef :: forall s n. IsGlobal (IndexedSymbol s n) => GlobalRef (IndexedSymbol s n)
knownIndexedGlobalRef = knownGlobalRef

mkSimpleGlobalRef :: CT.SymbolRepr s -> Maybe (SimpleGlobalRef s)
mkSimpleGlobalRef symb = lookupGlobalRefSym symb >>= \case
  SimpleGlobalRef sgr -> return sgr
  _ -> fail ""

mkGPRRef :: forall n. n <= 14 => NR.NatRepr n -> GPRRef n
mkGPRRef nr |
    NR.LeqProof <- NR.leqAdd2 (NR.leqProof nr (NR.knownNat @14)) (NR.leqRefl (NR.knownNat @1))
  , vn <- ValidNatRepr @GPRCtx nr
  , Some idx <- validNatToIndex knownSize vn
  , Refl <- gprIdxPrf idx
  = GPRRef' vn idx

withGPRRepr :: GPRRef n -> (n <= (CtxSize GPRCtx) - 1 => NR.NatRepr n -> a) -> a
withGPRRepr (GPRRef' vnr _) f  = withValidNatRepr knownSize vnr f

mkGPRGlobalRef :: forall n. n <= (CtxSize GPRCtx) - 1 => NR.NatRepr n -> GlobalRef (IndexedSymbol "GPRS" n)
mkGPRGlobalRef nr = GPRRef (mkGPRRef nr)

mkSIMDRef :: forall n. n <= 31 => NR.NatRepr n -> SIMDRef n
mkSIMDRef nr |
    NR.LeqProof <- NR.leqAdd2 (NR.leqProof nr (NR.knownNat @31)) (NR.leqRefl (NR.knownNat @1))
  , vn <- ValidNatRepr @SIMDCtx nr
  , Some idx <- validNatToIndex knownSize vn
  , Refl <- simdIdxPrf idx
  = SIMDRef' vn idx

withSIMDRepr :: SIMDRef n -> (n <= (CtxSize SIMDCtx) - 1 => NR.NatRepr n -> a) -> a
withSIMDRepr (SIMDRef' vnr _) f  = withValidNatRepr knownSize vnr f

mkSIMDGlobalRef :: forall n. n <= (CtxSize SIMDCtx) - 1 => NR.NatRepr n -> GlobalRef (IndexedSymbol "SIMD" n)
mkSIMDGlobalRef nr = SIMDRef (mkSIMDRef nr)

knownGlobalRef :: forall s
                . IsGlobal s
               => GlobalRef s
knownGlobalRef = fromJust $ lookupGlobalRefSym $ (CT.knownSymbol :: CT.SymbolRepr s)

instance TH.Lift (GlobalRef s) where
  lift gr = [e| knownGlobalRef :: GlobalRef $(TH.litT (TH.strTyLit (T.unpack $ CT.symbolRepr $ globalRefSymbol gr))) |]


_test :: GlobalRef "_PC"
_test = knownGlobalRef @"_PC"

_test2 :: GlobalsType "_PC" :~: WI.BaseBVType 32
_test2 = Refl

_testLift :: GlobalRef "_PC"
_testLift = $([e| knownGlobalRef @"_PC" |])
