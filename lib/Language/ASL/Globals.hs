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
  _ -> error "untrackedGlobals: template haskell error"

untrackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) UntrackedGlobalsCtx
untrackedGlobalReprs = FC.fmapFC (\gb -> LabeledValue (gbName gb) (gbType gb)) untrackedGlobals

trackedGlobals :: Assignment Global GlobalsCtx
trackedGlobals = case trackedGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) trackedGlobalBaseReprs -> gbs
  _ -> error "trackedGlobals: template haskell error"

simpleGlobalBaseReprs :: Assignment WI.BaseTypeRepr SimpleGlobalsCtx
simpleGlobalBaseReprs = $(mkReprFromGlobals simpleGlobals')

simpleGlobals :: Assignment Global SimpleGlobalsCtx
simpleGlobals = case simpleGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) simpleGlobalBaseReprs -> gbs
  _ -> error "simpleGlobals: template haskell error"

gprGlobalBaseReprs :: Assignment WI.BaseTypeRepr GPRCtx
gprGlobalBaseReprs = $(mkReprFromGlobals gprGlobals')

gprGlobals :: Assignment Global GPRCtx
gprGlobals = case gprGlobals' of
  Some gbs | Just Refl <- testEquality (FC.fmapFC gbType gbs) gprGlobalBaseReprs -> gbs
  _ -> error "gprGlobals: template haskell error"

simdGlobalBaseReprs :: Assignment WI.BaseTypeRepr SIMDCtx
simdGlobalBaseReprs = $(mkReprFromGlobals simdGlobals')

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

$(mkInstDeclsFromGlobals simpleGlobals')
$(mkSimpleInstDecls simpleGlobals')
$(mkInstDeclsFromGlobals gprGlobals')
$(mkInstDeclsFromGlobals simdGlobals')
$(mkInstDeclsFromGlobals (forSome memoryGlobal' $ \gb -> Some (empty :> gb)))

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
          -> LeqProofRepr MaxGPR n
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
           -> LeqProofRepr MaxSIMD n
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

type SimpleGlobalSymsCtx = $(mkAllGlobalSymsT simpleGlobals')

simpleGlobalRefs :: Assignment SimpleGlobalRef SimpleGlobalSymsCtx
simpleGlobalRefs = $(mkGlobalsE simpleGlobals'
    (\idx gb -> [e| SimpleGlobalRef' $(mkSymbolE (gbName gb)) $(liftIndex idx) |]))

type GPRIdxCtx = $(mkNatCtx (NR.intValue maxGPRRepr))

gprGlobalRefs :: Assignment GPRRef GPRIdxCtx
gprGlobalRefs = $(mkGlobalsE gprGlobals'
    (\idx gb -> [e| GPRRef' $(mkSymbolE (gbName gb)) (LeqProofRepr maxGPRRepr $(liftIndexNatRepr idx)) $(liftIndex idx) |]))

type SIMDIdxCtx = $(mkNatCtx (NR.intValue maxSIMDRepr))

simdGlobalRefs :: Assignment SIMDRef SIMDIdxCtx
simdGlobalRefs = $(mkGlobalsE simdGlobals'
    (\idx gb -> [e| SIMDRef' $(mkSymbolE (gbName gb)) (LeqProofRepr maxSIMDRepr $(liftIndexNatRepr idx)) $(liftIndex idx) |]))

memoryGlobalIdx :: Index GlobalsCtx (GlobalsType "__Memory")
memoryGlobalIdx = lastIndex $ (Ctx.size trackedGlobals)

memoryGlobalRef :: GlobalRef "__Memory"
memoryGlobalRef = MemoryRef memoryGlobalIdx


allGlobalRefs' :: Some (Assignment GlobalRef)
allGlobalRefs' = Ctx.fromList $
     FC.toListFC Some (FC.fmapFC SimpleGlobalRef simpleGlobalRefs)
  ++ (map (\(Some gpr) -> Some (GPRRef gpr)) $ FC.toListFC Some gprGlobalRefs)
  ++ (map (\(Some simd) -> Some (SIMDRef simd)) $ FC.toListFC Some simdGlobalRefs)
  ++ [Some memoryGlobalRef]

type GlobalSymsCtx = $(mkAllGlobalSymsT flatTrackedGlobals')

globalSymsReprs :: Assignment CT.SymbolRepr GlobalSymsCtx
globalSymsReprs = $(mkAllGlobalSymsE flatTrackedGlobals')

allGlobalRefs :: Assignment GlobalRef GlobalSymsCtx
allGlobalRefs = forSome allGlobalRefs' $ \gbs ->
  let syms = FC.fmapFC globalRefSymbol gbs
  in case testEquality syms globalSymsReprs of
    Just Refl -> gbs
    Nothing -> error $ "allGlobalRefs: template haskell error: Expected: " ++ show globalSymsReprs
      ++ "\nBut got:" ++ show syms

globalRefMap :: MapF CT.SymbolRepr GlobalRef
globalRefMap = MapF.fromList $
  FC.toListFC (\gb -> Pair (globalRefSymbol gb) gb) allGlobalRefs

gprTypePrf :: LeqProofRepr MaxGPR n
           -> GlobalsType (IndexedSymbol "GPR" n) :~: WI.BaseBVType 32
gprTypePrf vnr
  | Just gprRef <- lookupGlobalRefSym (gprSymbolRepr vnr)
  , Just Refl <- testEquality (globalRefRepr gprRef) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 32))
  = Refl
gprTypePrf _ = error "gprTypePrf: invalid gprs"

simdTypePrf :: LeqProofRepr MaxSIMD n
            -> GlobalsType (IndexedSymbol "SIMD" n) :~: WI.BaseBVType 128
simdTypePrf vnr
  | Just simdRef <- lookupGlobalRefSym (simdSymbolRepr vnr)
  , Just Refl <- testEquality (globalRefRepr simdRef) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 128))
  = Refl
simdTypePrf _ = error "simdTypePrf: invalid simds"

gprIdxPrf :: Index GPRCtx tp
          -> tp :~: WI.BaseBVType 32
gprIdxPrf idx
  | Just Refl <- testEquality (gprGlobalBaseReprs ! idx) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 32))
  = Refl
gprIdxPrf _ = error "gprIdxPrf: invalid gprs"

simdIdxPrf :: Index SIMDCtx tp
           -> tp :~: WI.BaseBVType 128
simdIdxPrf idx
  | Just Refl <- testEquality (simdGlobalBaseReprs ! idx) (CT.knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 128))
  = Refl
simdIdxPrf _ = error "simdIdxPrf: invalid simds"

data LeqProofRepr (maxn :: Nat) (n :: Nat)  where
  LeqProofRepr :: forall maxn n. (n <= maxn) => NR.NatRepr maxn -> NR.NatRepr n -> LeqProofRepr maxn n

deriving instance Show (LeqProofRepr maxn n)
deriving instance Eq (LeqProofRepr maxn n)

instance ShowF (LeqProofRepr maxn) where
  showF vnr = show vnr

instance TestEquality (LeqProofRepr maxn) where
  testEquality (LeqProofRepr _ nr) (LeqProofRepr _ nr') = testEquality nr nr'

instance OrdF (LeqProofRepr maxn) where
  compareF (LeqProofRepr _ nr) (LeqProofRepr _ nr') = compareF nr nr'

withLeqProofRepr :: forall n maxn a
                  . LeqProofRepr maxn n
                 -> (n <= maxn => NR.LeqProof n maxn -> NR.NatRepr maxn -> NR.NatRepr n -> a)
                 -> a
withLeqProofRepr (LeqProofRepr maxn n) f = f (NR.leqProof n maxn) maxn n

ctxSizeRepr :: forall ctx. Size ctx -> NR.NatRepr (CtxSize ctx)
ctxSizeRepr sz = case viewSize sz of
  ZeroSize -> NR.knownNat
  IncSize sz' -> NR.addNat (NR.knownNat @1) (ctxSizeRepr sz')

indexToBoundedNat :: forall ctx tp
                 . Size ctx
                -> Index ctx tp
                -> Some (LeqProofRepr (CtxSize ctx -1))
indexToBoundedNat sz idx |
    Just (Some nr) <- NR.someNat (indexVal idx)
  , Just NR.LeqProof  <- NR.isPosNat (ctxSizeRepr sz)
  , szRepr <- NR.decNat (ctxSizeRepr sz)
  , Just NR.LeqProof <- NR.testLeq nr szRepr
  = Some $ LeqProofRepr szRepr nr
indexToBoundedNat _ _ = error "indexToBoundedNat: bad index"

boundedNatToIndex :: forall ctx n
                   . Size ctx
                  -> LeqProofRepr (CtxSize ctx - 1) n
                  -> Some (Index ctx)
boundedNatToIndex sz (LeqProofRepr _ nr) = fromJust $ intIndex (fromIntegral $ NR.natValue nr) sz

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


data IndexedSymbolRepr (s :: Symbol) (n :: Nat) where
  IndexedSymbolRepr :: CT.SymbolRepr (IndexedSymbol s n) -> IndexedSymbolRepr s n
  deriving Show

instance ShowF (IndexedSymbolRepr s) where
  showF = show

gprSymbolReprMap :: MapF (LeqProofRepr MaxGPR) (IndexedSymbolRepr "GPR")
gprSymbolReprMap = MapF.fromList $
  $(mapNatsUpto (NR.intValue maxGPRRepr)
    [e| \nr -> Pair (LeqProofRepr maxGPRRepr nr) (IndexedSymbolRepr CT.knownSymbol) |])

gprSymbolRepr :: LeqProofRepr MaxGPR n -> CT.SymbolRepr (IndexedSymbol "GPR" n)
gprSymbolRepr vnr | Just (IndexedSymbolRepr symb) <- MapF.lookup vnr gprSymbolReprMap = symb
gprSymbolRepr vnr =
  error $ "gprSymbolRepr: invalid gprs: Failed to find:" ++ show vnr
    ++ " in: " ++ show gprSymbolReprMap

-- | Get the 'GPRRef' corresponding to the nth GPR, with an explicit 'NR.NatRepr' for n
mkGPRRef :: forall n. n <= MaxGPR => NR.NatRepr n -> GPRRef n
mkGPRRef nr
  | vnr <- LeqProofRepr maxGPRRepr nr
  , Refl <- gprTypePrf vnr
  , Some idx <- boundedNatToIndex (Ctx.size gprGlobals) vnr
  , Refl <- gprIdxPrf idx
  = GPRRef' (gprSymbolRepr vnr) vnr idx

-- | Get the 'GPRRef' corresponding to the nth GPR, with an implicit 'KnownNat' for n.
knownGPRRef :: forall n. KnownNat n => n <= MaxGPR => GPRRef n
knownGPRRef = mkGPRRef (NR.knownNat @n)

-- | View the components of a 'GPRRef', with sufficient type information to reconstruct it.
withGPRRef :: GPRRef n
            -> (n <= MaxGPR => GlobalsType (IndexedSymbol "GPR" n) ~ WI.BaseBVType 32
                => CT.SymbolRepr (IndexedSymbol "GPR" n)
                -> NR.NatRepr n
                -> a)
             -> a
withGPRRef (GPRRef' symb vnr _) f | Refl <- gprTypePrf vnr = withLeqProofRepr vnr (\_ _ -> f symb)

-- | Get the 'GlobalRef' corresponding to the nth GPR, with an explicit 'NR.NatRepr' for n.
mkGPRGlobalRef :: forall n. n <= MaxGPR => NR.NatRepr n -> GlobalRef (IndexedSymbol "GPR" n)
mkGPRGlobalRef nr = GPRRef (mkGPRRef nr)

-- | Get the 'GlobalRef' corresponding to the nth GPR, with an implicit 'KnownNat' for n
knownGPRGlobalRef :: forall n. KnownNat n => n <= MaxGPR => GlobalRef (IndexedSymbol "GPR" n)
knownGPRGlobalRef = GPRRef (knownGPRRef @n)

simdSymbolReprMap :: MapF (LeqProofRepr MaxSIMD) (IndexedSymbolRepr "SIMD")
simdSymbolReprMap = MapF.fromList $
  $(mapNatsUpto (NR.intValue maxSIMDRepr)
    [e| \nr -> Pair (LeqProofRepr maxSIMDRepr nr) (IndexedSymbolRepr CT.knownSymbol) |])

simdSymbolRepr :: LeqProofRepr MaxSIMD n -> CT.SymbolRepr (IndexedSymbol "SIMD" n)
simdSymbolRepr vnr | Just (IndexedSymbolRepr symb) <- MapF.lookup vnr simdSymbolReprMap = symb
simdSymbolRepr _ = error "simdSymbolRepr: invalid simds"


-- | Get the 'SIMDRef' corresponding to the nth SIMD register, with an explicit 'NR.NatRepr' for n.
mkSIMDRef' :: forall n. n <= MaxSIMD => NR.NatRepr n -> SIMDRef n
mkSIMDRef' nr
  | vnr <- LeqProofRepr maxSIMDRepr nr
  , Refl <- simdTypePrf vnr
  , Some idx <- boundedNatToIndex (Ctx.size simdGlobals) vnr
  , Refl <- simdIdxPrf idx
  = SIMDRef' (simdSymbolRepr vnr) vnr idx


-- | Get the 'SIMDRef' corresponding to the nth SIMD register, with an explicit 'NR.NatRepr' for n.
mkSIMDRef :: forall n. n <= MaxSIMD => NR.NatRepr n -> SIMDRef n
mkSIMDRef nr
  | vnr <- LeqProofRepr maxSIMDRepr nr
  , Some idx <- boundedNatToIndex (Ctx.size simdGlobalRefs) vnr
  , ref@(SIMDRef' _ vnr' _) <- simdGlobalRefs ! idx
  , Just Refl <- testEquality vnr vnr'
  = ref
mkSIMDRef _ = error $ "mkSIMDRef: incoherent simds"

-- | Get the 'SIMDRef' corresponding to the nth SIMD register, with an implicit 'KnownNat' for n.
knownSIMDRef :: forall n. KnownNat n => n <= MaxSIMD => SIMDRef n
knownSIMDRef = mkSIMDRef (NR.knownNat @n)

-- | View the components of a 'SIMDRef', with sufficient type information to reconstruct it.
withSIMDRef :: SIMDRef n
             -> (n <= MaxSIMD => GlobalsType (IndexedSymbol "SIMD" n) ~ WI.BaseBVType 128
                 => CT.SymbolRepr (IndexedSymbol "SIMD" n)
                 -> NR.NatRepr n
                 -> a)
             -> a
withSIMDRef (SIMDRef' symb vnr _) f | Refl <- simdTypePrf vnr = withLeqProofRepr vnr (\_ _ -> f symb)


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
