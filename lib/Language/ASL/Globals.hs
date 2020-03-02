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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -ddump-splices -ddump-to-file -dth-dec-file #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.ASL.Globals
  ( trackedGlobals
  , untrackedGlobals
  , untrackedGlobalReprs
  , trackedGlobalReprs
  , trackedGlobalBaseReprs
  , GlobalsCtx -- the Context corresponding to the structure of the globals in ASL
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
  , globalOfGlobalRef
  , simpleGlobalRefs
  , gprGlobalRefs
  , simdGlobalRefs
  , memoryGlobalRef
  , allGlobalRefs
  , GlobalSymsCtx -- All symbols for globals (with a unique symbol for each GPR and SIMD)
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
  , withGPRRef
  , withSIMDRef
  , consistencyCheck
  )

where

import           GHC.TypeLits

import           Control.Applicative ( Const(..) )
import           Control.Monad.Identity
import qualified Control.Monad.Except as ME

import           Data.Kind
import           Data.Proxy
import           Data.Void
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

-- from this package
import           Data.Parameterized.CtxFuns

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

import           Unsafe.Coerce



-- "GlobalsType" instances
$(mkGlobalsTypeInstDecls trackedGlobals')
$(mkGlobalsTypeInstDecls gprGlobals')
$(mkGlobalsTypeInstDecls simdGlobals')

-- "IsGlobal" instances
$(mkIsGlobalInstDecls flatTrackedGlobals')

-- "IsSimpleGlobal" instances
$(mkSimpleGlobalInstDecls simpleGlobals')

data GlobalsTypeWrapper :: TyFun Symbol WI.BaseType -> Type
type instance Apply GlobalsTypeWrapper s = GlobalsType s

data NatToRegSymWrapper :: Symbol -> TyFun Nat Symbol -> Type
type instance Apply (NatToRegSymWrapper s) n = AppendSymbol s (NatToSymbol n)

data NatToRegTypeWrapper :: Symbol -> TyFun Nat WI.BaseType -> Type
type instance Apply (NatToRegTypeWrapper s) n = GlobalsType (AppendSymbol s (NatToSymbol n))

type GlobalsTypeCtx (sh :: Ctx Symbol) = MapContext GlobalsTypeWrapper sh

type SimpleGlobalSymsCtx = $(mkAllGlobalSymsT simpleGlobals')
type UntrackedGlobalsCtx = $(mkTypeFromGlobals untrackedGlobals')
type SimpleGlobalsCtx = GlobalsTypeCtx SimpleGlobalSymsCtx
type GlobalSymsCtx = $(mkAllGlobalSymsT trackedGlobals')


type GPRIdxCtx = CtxUpTo MaxGPR
type GPRSymsUpToCtx n = MapContext (NatToRegSymWrapper "GPR") (CtxUpTo n)
type GPRSymsCtx = GPRSymsUpToCtx MaxGPR
type GPRCtx = GlobalsTypeCtx GPRSymsCtx

_gprCtxTest :: GPRCtx :~: CtxReplicate (WI.BaseBVType 32) (MaxGPR + 1)
_gprCtxTest = Refl

type SIMDIdxCtx = CtxUpTo MaxSIMD
type SIMDSymsUpToCtx n = MapContext (NatToRegSymWrapper "SIMD") (CtxUpTo n)
type SIMDSymsCtx = SIMDSymsUpToCtx MaxSIMD
type SIMDCtx = GlobalsTypeCtx SIMDSymsCtx

-- | The type-level symbols of all 'GlobalDef's.
type FlatGlobalSymsCtx =
  SimpleGlobalSymsCtx <+> GPRSymsCtx <+> SIMDSymsCtx ::> "__Memory"

_simdCtxTest :: SIMDCtx :~: CtxReplicate (WI.BaseBVType 128) (MaxSIMD + 1)
_simdCtxTest = Refl

-- | The Context corresponding to the structure of the globals in ASL,
-- (i.e. with GPRs and SIMDs in structs)
type GlobalsCtx = GlobalsTypeCtx GlobalSymsCtx

simpleEmbedding :: CtxEmbedding SimpleGlobalsCtx GlobalsCtx
simpleEmbedding =
  extendEmbeddingRight $ extendEmbeddingRight $ extendEmbeddingRight $ identityEmbedding (Ctx.size simpleGlobals)

untrackedGlobalBaseReprs :: Assignment WI.BaseTypeRepr UntrackedGlobalsCtx
untrackedGlobalBaseReprs = $(mkReprFromGlobals untrackedGlobals')

trackedGlobalBaseReprs :: Assignment WI.BaseTypeRepr GlobalsCtx
trackedGlobalBaseReprs = knownRepr

untrackedGlobals :: Assignment Global UntrackedGlobalsCtx
untrackedGlobals = case untrackedGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) untrackedGlobalBaseReprs -> gbs
  _ -> error "untrackedGlobals: template haskell error"

untrackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) UntrackedGlobalsCtx
untrackedGlobalReprs = FC.fmapFC (\gb -> LabeledValue (gbName gb) (gbType gb)) untrackedGlobals

trackedGlobals :: Assignment Global GlobalsCtx
trackedGlobals = case trackedGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) trackedGlobalBaseReprs -> gbs
  _ -> error "trackedGlobals: template haskell error"

simpleGlobalBaseReprs :: Assignment WI.BaseTypeRepr SimpleGlobalsCtx
simpleGlobalBaseReprs = knownRepr

simpleGlobals :: Assignment Global SimpleGlobalsCtx
simpleGlobals = case simpleGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) simpleGlobalBaseReprs -> gbs
  _ -> error "simpleGlobals: template haskell error"

gprGlobalBaseReprs :: Assignment WI.BaseTypeRepr GPRCtx
gprGlobalBaseReprs = knownRepr

gprGlobals :: Assignment Global GPRCtx
gprGlobals = case gprGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) gprGlobalBaseReprs -> gbs
  _ -> error "gprGlobals: template haskell error"

simdGlobalBaseReprs :: Assignment WI.BaseTypeRepr SIMDCtx
simdGlobalBaseReprs = knownRepr

simdGlobals :: Assignment Global SIMDCtx
simdGlobals = case simdGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) simdGlobalBaseReprs -> gbs
  _ -> error "simdGlobals: template haskell error"

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

-- Here we specify the 'GlobalRef' type, which serves as an abstraction over the internal
-- representation of the globals in ASL.

-- | A 'SimpleGlobalRef' is a reference to a single piece of
-- global state (i.e. a meta-state flag or the processor state).
data SimpleGlobalRef (s :: Symbol) where
  SimpleGlobalRef' :: CT.SymbolRepr s
                   -> Index SimpleGlobalsCtx (GlobalsType s)
                   -> SimpleGlobalRef s
  deriving (Eq, Show)

instance TestEquality SimpleGlobalRef where
  testEquality (SimpleGlobalRef' symb idx) (SimpleGlobalRef' symb' idx') = do
    Refl <- testEquality symb symb'
    Refl <- testEquality idx idx'
    return Refl

-- | A 'GPRRef' represents a reference to a particular general-purpose register.
data GPRRef (n :: Nat) where
  GPRRef' :: CT.SymbolRepr (IndexedSymbol "GPR" n)
          -> GeqProofRepr MaxGPR n
          -> Index GPRCtx (GlobalsType (IndexedSymbol "GPR" n))
          -> GPRRef n
  deriving (Eq, Show)

instance TestEquality GPRRef where
  testEquality (GPRRef' symb vnr idx) (GPRRef' symb' vnr' idx') = do
    Refl <- testEquality symb symb'
    Refl <- testEquality vnr vnr'
    Refl <- testEquality idx idx'
    return Refl

-- | A 'SIMDRef' represents a reference to a particular SIMD register.
data SIMDRef (n :: Nat) where
  SIMDRef' :: CT.SymbolRepr (IndexedSymbol "SIMD" n)
           -> GeqProofRepr MaxSIMD n
           -> Index SIMDCtx (GlobalsType (IndexedSymbol "SIMD" n))
           -> SIMDRef n
  deriving (Eq, Show)

instance TestEquality SIMDRef where
  testEquality (SIMDRef' symb vnr idx) (SIMDRef' symb' vnr' idx') = do
    Refl <- testEquality symb symb'
    Refl <- testEquality vnr vnr'
    Refl <- testEquality idx idx'
    return Refl

-- | A 'GlobalRef' refers to any single piece of global state tracked by the ASL semantics.
data GlobalRef (s :: Symbol) where
  SimpleGlobalRef :: SimpleGlobalRef s -> GlobalRef s
  GPRRef :: GPRRef n -> GlobalRef (IndexedSymbol "GPR" n)
  SIMDRef :: SIMDRef n -> GlobalRef (IndexedSymbol "SIMD" n)
  MemoryRef :: Index GlobalsCtx (GlobalsType "__Memory") -> GlobalRef "__Memory"
  -- ^ The distinguished global state variable representing memory.

deriving instance Show (GlobalRef s)

instance ShowF GlobalRef where
  showF = show

-- | Deep equality check on 'GlobalRef's. In general this is unnecessary since
-- we assume the symbols are distinct as an invariant (i.e. symbol equality implies ref equality).
deepTestRefEquality :: GlobalRef s -> GlobalRef s' -> Maybe (s :~: s')
deepTestRefEquality gr gr' = case (gr, gr') of
    (SimpleGlobalRef sgr, SimpleGlobalRef sgr') | Just Refl <- testEquality sgr sgr' -> Just Refl
    (GPRRef gpr, GPRRef gpr') | Just Refl <- testEquality gpr gpr' -> Just Refl
    (SIMDRef simd, SIMDRef simd') | Just Refl <- testEquality simd simd' -> Just Refl
    (MemoryRef idx, MemoryRef idx') | Just Refl <- testEquality idx idx' -> Just Refl
    _ -> Nothing

simpleGlobalRefs :: Assignment SimpleGlobalRef SimpleGlobalSymsCtx
simpleGlobalRefs =
  let
    go :: Index SimpleGlobalSymsCtx s -> CT.SymbolRepr s -> Identity (SimpleGlobalRef s)
    go idx symb = return $
      SimpleGlobalRef' symb (mapContextIndex (Proxy @GlobalsTypeWrapper) knownSize idx)
  in runIdentity $ Ctx.traverseWithIndex go knownRepr

gprGlobalRefs :: Assignment GPRRef GPRIdxCtx
gprGlobalRefs =
  let
    go :: Index GPRIdxCtx n -> NR.NatRepr n -> Identity (GPRRef n)
    go idx nr = return $
      GPRRef' (mkIndexedSymbol (CT.knownSymbol @"GPR") nr)
              (upToProofRepr maxGPRRepr ! idx)
              (mapContextIndex (Proxy @(NatToRegTypeWrapper "GPR")) knownSize idx)
  in runIdentity $ Ctx.traverseWithIndex go knownRepr

simdGlobalRefs :: Assignment SIMDRef SIMDIdxCtx
simdGlobalRefs =
  let
    go :: Index SIMDIdxCtx n -> NR.NatRepr n -> Identity (SIMDRef n)
    go idx nr = return $
      SIMDRef' (mkIndexedSymbol (CT.knownSymbol @"SIMD") nr)
               (upToProofRepr maxSIMDRepr ! idx)
               (mapContextIndex (Proxy @(NatToRegTypeWrapper "SIMD")) knownSize idx)
  in runIdentity $ Ctx.traverseWithIndex go knownRepr

memoryGlobalIdx :: Index GlobalsCtx (GlobalsType "__Memory")
memoryGlobalIdx = lastIndex $ (Ctx.size trackedGlobals)

memoryGlobalRef :: GlobalRef "__Memory"
memoryGlobalRef = MemoryRef memoryGlobalIdx

allGlobalRefs :: Assignment GlobalRef FlatGlobalSymsCtx
allGlobalRefs =
       FC.fmapFC SimpleGlobalRef simpleGlobalRefs
  <++> applyMapContext (Proxy @(NatToRegSymWrapper "GPR")) GPRRef gprGlobalRefs
  <++> applyMapContext (Proxy @(NatToRegSymWrapper "SIMD")) SIMDRef simdGlobalRefs
  :> memoryGlobalRef

globalRefMap :: MapF CT.SymbolRepr GlobalRef
globalRefMap = MapF.fromList $
  FC.toListFC (\gb -> Pair (globalRefSymbol gb) gb) allGlobalRefs

gprIdxPrf :: Index GPRCtx tp
          -> tp :~: WI.BaseBVType 32
gprIdxPrf idx = replicatedCtxPrf (NR.incNat maxGPRRepr) knownSize idx

simdIdxPrf :: Index SIMDCtx tp
           -> tp :~: WI.BaseBVType 128
simdIdxPrf idx = replicatedCtxPrf (NR.incNat maxSIMDRepr) knownSize idx

ctxSizeRepr :: forall ctx. Size ctx -> NR.NatRepr (CtxSize ctx)
ctxSizeRepr sz = case viewSize sz of
  ZeroSize -> NR.knownNat
  IncSize sz' -> NR.addNat (NR.knownNat @1) (ctxSizeRepr sz')

-- | Index into the set of all tracked globals - pointing to the struct that contains all of the GPRs
gprGlobalIndex :: Index GlobalsCtx (WI.BaseStructType GPRCtx)
gprGlobalIndex = skipIndex $ skipIndex $ lastIndex $ decSize $ decSize $ (Ctx.size trackedGlobals)

-- | Index into the set of all tracked globals - pointing to the struct that contains all of the SIMDs
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
  GPRRef (GPRRef' _ _ idx) -> resolveidx (asn ! gprGlobalIndex) idx
  SIMDRef (SIMDRef' _ _ idx) -> resolveidx (asn ! simdGlobalIdx) idx
  MemoryRef idx -> asn ! idx

-- | Get the original 'Global' used to specify the given 'GlobalRef'.
globalOfGlobalRef :: GlobalRef s -> Global (GlobalsType s)
globalOfGlobalRef gr = case gr of
  SimpleGlobalRef (SimpleGlobalRef' _ idx) -> simpleGlobals ! idx
  GPRRef (GPRRef' _ _ idx) -> gprGlobals ! idx
  SIMDRef (SIMDRef' _ _ idx) -> simdGlobals ! idx
  MemoryRef idx -> trackedGlobals ! idx

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
  GPRRef (GPRRef' symb _ _) -> symb
  SIMDRef (SIMDRef' symb _ _) -> symb
  MemoryRef _ -> CT.knownSymbol

globalRefRepr :: GlobalRef s -> WI.BaseTypeRepr (GlobalsType s)
globalRefRepr = resolveGlobalRef (\(WI.BaseStructRepr repr) idx -> repr ! idx) trackedGlobalBaseReprs

-- Here we explicitly assume that each symbol represents a unique global ref
instance TestEquality GlobalRef where
  testEquality gr1 gr2 = testEquality (globalRefSymbol gr1) (globalRefSymbol gr2)

instance OrdF GlobalRef where
  compareF gr1 gr2 = compareF (globalRefSymbol gr1) (globalRefSymbol gr2)

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

knownSimpleGlobalRef :: forall s. IsSimpleGlobal s => SimpleGlobalRef s
knownSimpleGlobalRef = case lookupGlobalRefSym (CT.knownSymbol @s) of
  Just (SimpleGlobalRef sgr) -> sgr
  Nothing -> error $ "knownSimpleGlobalRef: incoherent simple globals"


gprSymbolRepr :: GeqProofRepr MaxGPR n -> CT.SymbolRepr (IndexedSymbol "GPR" n)
gprSymbolRepr (GeqProofRepr _ n) =
  case mkGPRRef n of
    GPRRef' symb _ _ -> symb

-- | Get the 'GPRRef' corresponding to the nth GPR, with an explicit 'NR.NatRepr' for n
mkGPRRef :: forall n. n <= MaxGPR => NR.NatRepr n -> GPRRef n
mkGPRRef nr
  | vnr <- GeqProofRepr maxGPRRepr nr
  , idx <- boundedNatUpToIndex vnr
  = gprGlobalRefs ! idx

-- | Get the 'GPRRef' corresponding to the nth GPR, with an implicit 'KnownNat' for n.
knownGPRRef :: forall n. KnownNat n => n <= MaxGPR => GPRRef n
knownGPRRef = mkGPRRef (NR.knownNat @n)

-- | Evidence that the given symbols and nat are all wellformed with respect to the
-- 'GlobalsType' class.
-- e.g. IndexedGlobalsTypeRepr "GPR" 1 "GPR1" (BaseBVType 32)
data IndexedGlobalsTypeProof (s :: Symbol) (tp :: WI.BaseType)  (s' :: Symbol) where
  IndexedGlobalsTypeProof :: forall s n s'. IndexedGlobalsTypeProof s (GlobalsType (IndexedSymbol s' n)) (IndexedSymbol s' n)

gprTypePrf' :: Assignment (IndexedGlobalsTypeProof "GPR" (WI.BaseBVType 32)) GPRSymsCtx
gprTypePrf' =
  FC.fmapFC mkTypeRepr (applyMapContext (Proxy @(NatToRegSymWrapper "GPR")) GPRRef gprGlobalRefs)
  where
    mkTypeRepr :: GlobalRef s -> IndexedGlobalsTypeProof "GPR" (WI.BaseBVType 32) s
    mkTypeRepr (GPRRef (GPRRef' symb (GeqProofRepr _ n) idx))
      | Refl <- gprIdxPrf idx
      , (nr :: NR.NatRepr n) <- n
      = IndexedGlobalsTypeProof @"GPR" @n
    mkTypeRepr _ = error "impossible"

gprTypePrf :: forall n
            . NR.NatRepr n
           -> Index GPRCtx (GlobalsType (IndexedSymbol "GPR" n))
           -> GlobalsType (IndexedSymbol "GPR" n) :~: WI.BaseBVType 32
gprTypePrf n idx
  | IndexApplied idx' <- getIndexApplied (Proxy @(GlobalsTypeWrapper)) (Proxy @GPRSymsCtx) knownSize idx
  , IndexedGlobalsTypeProof <- gprTypePrf' ! idx'
  = Refl

-- | View the components of a 'GPRRef', with sufficient type information to reconstruct it.
withGPRRef :: forall n a
            . GPRRef n
            -> (n <= MaxGPR => GlobalsType (IndexedSymbol "GPR" n) ~ WI.BaseBVType 32
                => CT.SymbolRepr (IndexedSymbol "GPR" n)
                -> NR.NatRepr n
                -> a)
             -> a
withGPRRef (GPRRef' symb vnr@(GeqProofRepr _ n) idx) f
  | Refl <- gprTypePrf n idx
  = withGeqProofRepr vnr (\_ _ -> f symb)

-- | Get the 'GlobalRef' corresponding to the nth GPR, with an explicit 'NR.NatRepr' for n.
mkGPRGlobalRef :: forall n. n <= MaxGPR => NR.NatRepr n -> GlobalRef (IndexedSymbol "GPR" n)
mkGPRGlobalRef nr = GPRRef (mkGPRRef nr)

-- | Get the 'GlobalRef' corresponding to the nth GPR, with an implicit 'KnownNat' for n
knownGPRGlobalRef :: forall n. KnownNat n => n <= MaxGPR => GlobalRef (IndexedSymbol "GPR" n)
knownGPRGlobalRef = GPRRef (knownGPRRef @n)

simdSymbolRepr :: GeqProofRepr MaxSIMD n -> CT.SymbolRepr (IndexedSymbol "SIMD" n)
simdSymbolRepr (GeqProofRepr _ n) =
  case mkSIMDRef n of
    SIMDRef' symb _ _ -> symb

-- | Get the 'SIMDRef' corresponding to the nth SIMD register, with an explicit 'NR.NatRepr' for n.
mkSIMDRef :: forall n. n <= MaxSIMD => NR.NatRepr n -> SIMDRef n
mkSIMDRef nr
  | vnr <- GeqProofRepr maxSIMDRepr nr
  , idx <- boundedNatUpToIndex vnr
  = simdGlobalRefs ! idx

-- | Get the 'SIMDRef' corresponding to the nth SIMD register, with an implicit 'KnownNat' for n.
knownSIMDRef :: forall n. KnownNat n => n <= MaxSIMD => SIMDRef n
knownSIMDRef = mkSIMDRef (NR.knownNat @n)

simdTypePrf' :: Assignment (IndexedGlobalsTypeProof "SIMD" (WI.BaseBVType 128)) SIMDSymsCtx
simdTypePrf' =
  FC.fmapFC mkTypeRepr (applyMapContext (Proxy @(NatToRegSymWrapper "SIMD")) SIMDRef simdGlobalRefs)
  where
    mkTypeRepr :: GlobalRef s -> IndexedGlobalsTypeProof "SIMD" (WI.BaseBVType 128) s
    mkTypeRepr (SIMDRef (SIMDRef' symb (GeqProofRepr _ n) idx))
      | Refl <- simdIdxPrf idx
      , (nr :: NR.NatRepr n) <- n
      = IndexedGlobalsTypeProof @"SIMD" @n
    mkTypeRepr _ = error "impossible"

simdTypePrf :: forall n
            . NR.NatRepr n
           -> Index SIMDCtx (GlobalsType (IndexedSymbol "SIMD" n))
           -> GlobalsType (IndexedSymbol "SIMD" n) :~: WI.BaseBVType 128
simdTypePrf n idx
  | IndexApplied idx' <- getIndexApplied (Proxy @(GlobalsTypeWrapper)) (Proxy @SIMDSymsCtx) knownSize idx
  , IndexedGlobalsTypeProof <- simdTypePrf' ! idx'
  = Refl

-- | View the components of a 'SIMDRef', with sufficient type information to reconstruct it.
withSIMDRef :: SIMDRef n
             -> (n <= MaxSIMD => GlobalsType (IndexedSymbol "SIMD" n) ~ WI.BaseBVType 128
                 => CT.SymbolRepr (IndexedSymbol "SIMD" n)
                 -> NR.NatRepr n
                 -> a)
             -> a
withSIMDRef (SIMDRef' symb vnr@(GeqProofRepr _ n) idx) f
  | Refl <- simdTypePrf n idx
  = withGeqProofRepr vnr (\_ _ -> f symb)


mkSIMDGlobalRef :: forall n. n <= MaxSIMD => NR.NatRepr n -> GlobalRef (IndexedSymbol "SIMD" n)
mkSIMDGlobalRef nr = SIMDRef (mkSIMDRef nr)

knownSIMDGlobalRef :: forall n. KnownNat n => n <= MaxSIMD => GlobalRef (IndexedSymbol "SIMD" n)
knownSIMDGlobalRef = SIMDRef (knownSIMDRef @n)

knownGlobalRef :: forall s
                . IsGlobal s
               => GlobalRef s
knownGlobalRef = fromJust $ lookupGlobalRefSym $ (CT.knownSymbol :: CT.SymbolRepr s)

instance TH.Lift (GlobalRef s) where
  lift gr = [e| knownGlobalRef :: GlobalRef $(TH.litT (TH.strTyLit (T.unpack $ CT.symbolRepr $ globalRefSymbol gr))) |]


-- | Various static checks that ensure everything has been instantiated correctly.
staticConsistencyCheck :: () -> Bool
staticConsistencyCheck _
  | pcGref <- knownGlobalRef @"_PC"
  , SimpleGlobalRef pcSref <- knownGlobalRef @"_PC"
  , (pcSref' ::  SimpleGlobalRef "_PC") <- knownSimpleGlobalRef @"_PC"
  , (pcRepr :: WI.BaseTypeRepr (WI.BaseBVType 32)) <- globalRefRepr pcGref
  , Just Refl <- testEquality pcSref pcSref'
  , gpr13GRef <- knownGlobalRef @"GPR13"
  , gpr13Ref' <- knownGPRRef @13
  , gpr13GRef' <- knownGPRGlobalRef @13
  , Nothing <- testEquality pcGref gpr13GRef
  , Just Refl <- testEquality $([e| knownGlobalRef @"_PC" |]) pcGref
  , Just Refl <- testEquality gpr13GRef (GPRRef gpr13Ref')
  , Just Refl <- testEquality gpr13GRef' gpr13GRef
  , simd25Ref <- knownGlobalRef @"SIMD25"
  , simd25Ref' <- knownSIMDRef @25
  , Just Refl <- testEquality simd25Ref (SIMDRef simd25Ref')
  , memRef <- knownGlobalRef @"__Memory"
  , Nothing <- testEquality memoryGlobalRef simd25Ref
  , Just Refl <- testEquality memRef memoryGlobalRef
  = True
staticConsistencyCheck _ = False

-- | True if the set of globals is internally consistent: each global
-- can be successfully retrieved by name and has the expected content.
consistencyCheck :: Bool
consistencyCheck =
  FC.allFC (isJust . checkEq) allGlobalRefs && (staticConsistencyCheck ())
  where
    checkEq :: GlobalRef s -> Maybe ()
    checkEq gr = do
      gr' <- lookupGlobalRefSym (globalRefSymbol gr)
      Refl <- deepTestRefEquality gr gr'
      case gr of
        SIMDRef simdRef -> withSIMDRef simdRef $ \symb n -> do
          gr'' <- lookupGlobalRefSym symb
          Refl <- deepTestRefEquality gr gr''
          Refl <- testEquality (mkSIMDRef n) simdRef
          Refl <- deepTestRefEquality (mkSIMDGlobalRef n) gr
          return ()
        GPRRef gprRef -> withGPRRef gprRef $ \symb n -> do
          gr'' <- lookupGlobalRefSym symb
          Refl <- deepTestRefEquality gr gr''
          Refl <- testEquality (mkGPRRef n) gprRef
          Refl <- deepTestRefEquality (mkGPRGlobalRef n) gr
          return ()
        _ -> return ()
