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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -ddump-splices -ddump-to-file -dth-dec-file #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.ASL.Globals
  ( Global(..)
  , GlobalsType
  , IndexedSymbol
  , GlobalRef(..)
  , SimpleGlobalRef
  , GPRRef
  , SIMDRef
  -- the BaseType of globals corresponding to their structure of the globals in ASL
  , GlobalsCtx
  -- all tracked globals (with each register set as a single struct)
  , trackedGlobals
  , trackedGlobalReprs
  -- the BaseType of the untracked globals
  , UntrackedGlobalsCtx
  -- all untracked globals
  , untrackedGlobals
  , untrackedGlobalReprs
  -- environment of statically-known (untracked) globals
  , staticGlobals
  -- compute a mapping from a list of named globals to the global struct
  , getGlobalsSubMap
  -- find a 'Global' based on its name and type.
  , lookupGlobal
  -- Type-level list of all globals
  , GlobalSymsCtx
  -- Structured view of the globals, with registers as arrays
  , StructGlobalSymsCtx
  , StructGlobalsCtx
  , allGlobalRefs

  -- All specified 'GlobalRefs'
  , simpleGlobalRefs
  , gprGlobalRefs
  , simdGlobalRefs
  , memoryGlobalRef

  -- accessing the data of a 'GlobalRef'
  , withGPRRef
  , withSIMDRef
  , globalRefSymbol
  , globalRefRepr
  , globalOfGlobalRef
  , globalRefIndex

  -- check if a given global is a specific (known) one
  , testGlobalEq

  -- making 'GlobalRef's at runtime
  , mkGlobalRef
  , lookupGlobalRefSymbol
  , lookupGlobalRef
  , mkSimpleGlobalRef
  , mkGPRRef
  , mkGPRGlobalRef
  , mkSIMDRef
  , mkSIMDGlobalRef

  -- making 'GlobalRef's for statically-known globals
  , knownGlobalRef
  , knownSimpleGlobalRef
  , knownSIMDGlobalRef
  , knownGPRGlobalRef

  -- pre and post conditions based
  -- on the constraints of the globals
  , getPrecond
  , getPostcond
  -- final self-test for this module
  , consistencyCheck
  )

where

import           GHC.TypeLits
import           Data.Constraint

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
import           Lang.Crucible.Types ( SymbolRepr, knownSymbol )

import           Language.ASL.StaticExpr
import           Language.ASL.Signature
import           Language.ASL.Types

import           Language.ASL.Globals.Types
import           Language.ASL.Globals.Definitions

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

import           Unsafe.Coerce

-- Types for all untracked globals
type UntrackedGlobalsCtx = $(mkTypeFromGlobals untrackedGlobals')

-- "GlobalsType" instances
$(mkGlobalsTypeInstDecls trackedGlobals')
$(mkGlobalsTypeInstDecls gprGlobals')
$(mkGlobalsTypeInstDecls simdGlobals')



type SimpleGlobalSymsCtx = $(mkAllGlobalSymsT simpleGlobals')
type SimpleGlobalsCtx = GlobalsTypeCtx SimpleGlobalSymsCtx

type GlobalSymsCtx = $(mkAllGlobalSymsT flatTrackedGlobals')
type GlobalsCtx = GlobalsTypeCtx GlobalSymsCtx

type GPRIdxCtx = CtxUpTo MaxGPR
type GPRSymsCtx = MapContext (NatToRegSymWrapper "_R") GPRIdxCtx

type SIMDIdxCtx = CtxUpTo MaxSIMD
type SIMDSymsCtx = MapContext (NatToRegSymWrapper "_V") SIMDIdxCtx


class KnownIndex GlobalSymsCtx s => IsGlobal s
instance KnownIndex GlobalSymsCtx s => IsGlobal s

class (IsGlobal s, KnownIndex SimpleGlobalSymsCtx s) => IsSimpleGlobal s
instance (IsGlobal s, KnownIndex SimpleGlobalSymsCtx s) => IsSimpleGlobal s

type GPRConstraints n =
  ( IsGlobal (IndexedSymbol "_R" n)
  , KnownIndex GPRIdxCtx n
  , GlobalsType (IndexedSymbol "_R" n) ~ WI.BaseBVType 32
  , n <= MaxGPR
  )

class GPRConstraints n => IsGPR n
instance GPRConstraints n => IsGPR n

natToGPR :: forall n. NR.NatRepr n -> (n <= MaxGPR) :- IsGPR n
natToGPR n = forallUpTo (Proxy @IsGPR) (Proxy @MaxGPR) n

type SIMDConstraints n =
  ( IsGlobal (IndexedSymbol "_V" n)
  , KnownIndex SIMDIdxCtx n
  , GlobalsType (IndexedSymbol "_V" n) ~ WI.BaseBVType 128
  , n <= MaxSIMD
  )

class SIMDConstraints n => IsSIMD n
instance SIMDConstraints n => IsSIMD n

natToSIMD :: forall n. NR.NatRepr n -> (n <= MaxSIMD) :- IsSIMD n
natToSIMD n = forallUpTo (Proxy @IsSIMD) (Proxy @MaxSIMD) n

-- | Test the shape of the globals signature.
_testDistinct :: (( DistinctCtx SimpleGlobalSymsCtx
                  , DistinctCtx GPRIdxCtx
                  , DistinctCtx SIMDIdxCtx
                  , DistinctCtx GlobalSymsCtx
                  , ForallCtx IsGPR GPRIdxCtx
                  , ForallCtx IsSIMD SIMDIdxCtx
                  ) => f)
                 -> f
_testDistinct f = f

-- Symbols for the globals as they appear in the ASL global struct
type StructGlobalSymsCtx = SimpleGlobalSymsCtx ::> "GPRS" ::> "SIMDS" ::> "__Memory"
type StructGlobalsCtx = GlobalsTypeCtx StructGlobalSymsCtx

data GlobalsTypeWrapper :: TyFun Symbol WI.BaseType -> Type
type instance Apply GlobalsTypeWrapper s = GlobalsType s

data NatToRegSymWrapper :: Symbol -> TyFun Nat Symbol -> Type
type instance Apply (NatToRegSymWrapper s) n = AppendSymbol s (NatToSymbol n)

data NatToRegTypeWrapper :: Symbol -> TyFun Nat WI.BaseType -> Type
type instance Apply (NatToRegTypeWrapper s) n = GlobalsType (AppendSymbol s (NatToSymbol n))

type GlobalsTypeCtx (sh :: Ctx Symbol) = MapContext GlobalsTypeWrapper sh

untrackedGlobals :: Assignment Global UntrackedGlobalsCtx
untrackedGlobals = forSome untrackedGlobals' $ \gbs ->
  case testEquality (FC.fmapFC gbType gbs) (knownRepr :: Assignment WI.BaseTypeRepr UntrackedGlobalsCtx) of
    Just Refl -> gbs
    _ -> error "untrackedGlobals: template haskell error"

untrackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) UntrackedGlobalsCtx
untrackedGlobalReprs = FC.fmapFC (\gb -> LabeledValue (gbName gb) (gbType gb)) untrackedGlobals

-- | All tracked globals (with each register set as a single struct)
trackedGlobals :: Assignment Global StructGlobalsCtx
trackedGlobals = forSome trackedGlobals' $ \gbs ->
  case testEquality (FC.fmapFC gbType gbs) (knownRepr :: Assignment WI.BaseTypeRepr StructGlobalsCtx) of
    Just Refl -> gbs
    _ -> error "trackedGlobals: template haskell error"

flatTrackedGlobals :: Assignment Global GlobalsCtx
flatTrackedGlobals = forSome flatTrackedGlobals' $ \gbs ->
  case testEquality (FC.fmapFC gbType gbs) (knownRepr :: Assignment WI.BaseTypeRepr GlobalsCtx) of
    Just Refl -> gbs
    _ -> error "flatTrackedGlobals: template haskell error"

trackedGlobalReprs :: Assignment (LabeledValue T.Text WI.BaseTypeRepr) StructGlobalsCtx
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

globalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index StructGlobalsCtx)
globalsMapIndexF = mkMapIndexF trackedGlobals

untrackedGlobalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index UntrackedGlobalsCtx)
untrackedGlobalsMapIndexF = mkMapIndexF untrackedGlobals

lookupUntrackedGlobal :: LabeledValue T.Text WI.BaseTypeRepr tp -> Maybe (Global tp)
lookupUntrackedGlobal lbl = (\idx -> untrackedGlobals ! idx) <$> MapF.lookup lbl untrackedGlobalsMapIndexF

lookupTrackedGlobal :: LabeledValue T.Text WI.BaseTypeRepr tp
                    -> Maybe (Global tp)
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
                 -> m (MapF (Index StructGlobalsCtx) (Index ctx))
getGlobalsSubMap reprs = do
  pairs <- traverseWithIndex mkEntry reprs
  return $ MapF.fromList $ catMaybes $ FC.toListFC (\(Const c) -> c) pairs
  where
    mkEntry :: Index ctx tp -> LabeledValue T.Text WI.BaseTypeRepr tp -> m (Const (Maybe (Pair (Index StructGlobalsCtx) (Index ctx))) tp)
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
  SimpleGlobalRef' :: IsSimpleGlobal s
                   => SymbolRepr s
                   -> SimpleGlobalRef s

deriving instance Show (SimpleGlobalRef s)

instance TestEquality SimpleGlobalRef where
  testEquality (SimpleGlobalRef' s) (SimpleGlobalRef' s') = testEquality s s'

instance Eq (SimpleGlobalRef s) where
  ref == ref' = isJust $ testEquality ref ref'


withSimpleGlobalRef :: SimpleGlobalRef s
                    -> (IsSimpleGlobal s
                       => CT.SymbolRepr s
                       -> f)
                    -> f
withSimpleGlobalRef (SimpleGlobalRef' symb) f = f symb

mkSimpleGlobalRef :: IsSimpleGlobal s => CT.SymbolRepr s -> SimpleGlobalRef s
mkSimpleGlobalRef symb = SimpleGlobalRef' symb

knownSimpleGlobalRef :: IsSimpleGlobal s => KnownSymbol s => SimpleGlobalRef s
knownSimpleGlobalRef = mkSimpleGlobalRef knownSymbol

-- | A 'GPRRef' represents a reference to a particular general-purpose register.
data GPRRef (n :: Nat) where
  GPRRef' :: (IsGPR n, n <= MaxGPR) => NR.NatRepr n -> GPRRef n

deriving instance Eq (GPRRef n)
deriving instance Show (GPRRef n)

instance TestEquality GPRRef where
  testEquality (GPRRef' n) (GPRRef' n') = testEquality n n'

withGPRRef :: GPRRef n
           -> (IsGPR n => NR.NatRepr n -> f)
           -> f
withGPRRef (GPRRef' n) f = f n

mkGPRRef :: forall n. n <= MaxGPR => NR.NatRepr n -> GPRRef n
mkGPRRef n = (GPRRef' n) \\ natToGPR n

knownGPRRef :: forall n. n <= MaxGPR => KnownNat n => GPRRef n
knownGPRRef = mkGPRRef @n NR.knownNat

-- | A 'SIMDRef' represents a reference to a particular SIMD register.
data SIMDRef (n :: Nat) where
  SIMDRef' :: (IsSIMD n, n <= MaxSIMD) => NR.NatRepr n -> SIMDRef n

deriving instance Eq (SIMDRef n)
deriving instance Show (SIMDRef n)

withSIMDRef :: SIMDRef n
            -> (IsSIMD n => n <= MaxSIMD => NR.NatRepr n -> f)
            -> f
withSIMDRef (SIMDRef' n) f = f n

mkSIMDRef :: forall n. n <= MaxSIMD => NR.NatRepr n -> SIMDRef n
mkSIMDRef n = (SIMDRef' n) \\ natToSIMD n

knownSIMDRef :: forall n. IsSIMD n => KnownNat n => SIMDRef n
knownSIMDRef = mkSIMDRef @n NR.knownNat

instance TestEquality SIMDRef where
  testEquality (SIMDRef' n) (SIMDRef' n') = testEquality n n'

-- | A 'GlobalRef' refers to any single piece of global state tracked by the ASL semantics.
data GlobalRef (s :: Symbol) where
  SimpleGlobalRef :: SimpleGlobalRef s -> GlobalRef s
  GPRRef :: GPRRef n -> GlobalRef (IndexedSymbol "_R" n)
  SIMDRef :: SIMDRef n -> GlobalRef (IndexedSymbol "_V" n)
  MemoryRef :: GlobalRef "__Memory"
  -- ^ The distinguished global state variable representing memory.

memoryGlobalRef :: GlobalRef "__Memory"
memoryGlobalRef = MemoryRef



mkGPRGlobalRef :: forall n. IsGPR n => NR.NatRepr n -> GlobalRef (IndexedSymbol "_R" n)
mkGPRGlobalRef n = GPRRef (mkGPRRef n)

knownGPRGlobalRef :: forall n. IsGPR n => KnownNat n => GlobalRef (IndexedSymbol "_R" n)
knownGPRGlobalRef = mkGPRGlobalRef @n NR.knownNat

mkSIMDGlobalRef :: forall n. IsSIMD n => NR.NatRepr n -> GlobalRef (IndexedSymbol "_V" n)
mkSIMDGlobalRef n = SIMDRef (mkSIMDRef n)

knownSIMDGlobalRef :: forall n. IsSIMD n => KnownNat n => GlobalRef (IndexedSymbol "_V" n)
knownSIMDGlobalRef = mkSIMDGlobalRef @n NR.knownNat

instance TestEquality GlobalRef where
  testEquality gref gref' = case (gref, gref') of
    (SimpleGlobalRef ref, SimpleGlobalRef ref') -> testEquality ref ref'
    (GPRRef ref, GPRRef ref') | Just Refl <- testEquality ref ref' -> Just Refl
    (SIMDRef ref, SIMDRef ref') | Just Refl <- testEquality ref ref' -> Just Refl
    (MemoryRef, MemoryRef) -> Just Refl
    _ -> Nothing

deriving instance Show (GlobalRef s)

instance ShowF GlobalRef where
  showF = show

withGlobalRef :: GlobalRef s -> (IsGlobal s => f) -> f
withGlobalRef gpr f = case gpr of
  SimpleGlobalRef ref -> withSimpleGlobalRef ref $ \_ -> f
  GPRRef ref -> withGPRRef ref $ \_ -> f
  SIMDRef ref -> withSIMDRef ref $ \_ -> f
  MemoryRef -> f

simpleGlobalRefs :: Assignment SimpleGlobalRef SimpleGlobalSymsCtx
simpleGlobalRefs =
  mapForallCtx (Proxy @(IsSimpleGlobal)) mkSimpleGlobalRef (knownRepr :: Assignment CT.SymbolRepr SimpleGlobalSymsCtx)

gprGlobalRefs :: Assignment GPRRef GPRIdxCtx
gprGlobalRefs =
  mapForallCtx (Proxy @(IsGPR)) mkGPRRef (knownRepr :: Assignment NR.NatRepr GPRIdxCtx)

simdGlobalRefs :: Assignment SIMDRef SIMDIdxCtx
simdGlobalRefs =
  mapForallCtx (Proxy @(IsSIMD)) mkSIMDRef (knownRepr :: Assignment NR.NatRepr SIMDIdxCtx)

data AllGlobalSig simple gprs simds mem =
  AllGlobalSig { aSimpleGlobalRefs :: Assignment simple SimpleGlobalSymsCtx
               , aGPRGlobalRefs :: Assignment gprs GPRIdxCtx
               , aSIMDGlobalRefs :: Assignment simds SIMDIdxCtx
               , aMemRef :: mem "__Memory"
               }

allGlobalRefsSig :: AllGlobalSig SimpleGlobalRef GPRRef SIMDRef SymbolRepr
allGlobalRefsSig = AllGlobalSig simpleGlobalRefs gprGlobalRefs simdGlobalRefs knownSymbol

mapAllGlobalRefsSig :: (forall s. IsSimpleGlobal s => simple s -> simple' s)
                    -> (forall n. IsGPR n => gprs n -> gprs' n)
                    -> (forall n. IsSIMD n => simds n -> simds' n)
                    -> (mem "__Memory" -> mem' "__Memory")
                    -> AllGlobalSig simple gprs simds mem
                    -> AllGlobalSig simple' gprs' simds' mem'
mapAllGlobalRefsSig fsimple fgprs fsimds fmem (AllGlobalSig simple gprs simds mem) =
  AllGlobalSig
  (mapForallCtx (Proxy @(IsSimpleGlobal)) fsimple simple)
  (mapForallCtx (Proxy @(IsGPR)) fgprs gprs)
  (mapForallCtx (Proxy @(IsSIMD)) fsimds simds)
  (fmem mem)

allGlobalRefs :: Assignment GlobalRef GlobalSymsCtx
allGlobalRefs =
  (FC.fmapFC SimpleGlobalRef simpleGlobalRefs
  <++> applyMapContext (Proxy @(NatToRegSymWrapper "_R")) GPRRef gprGlobalRefs
  <++> applyMapContext (Proxy @(NatToRegSymWrapper "_V")) SIMDRef simdGlobalRefs
  ):> memoryGlobalRef

knownGlobalRef :: forall s. IsGlobal s => GlobalRef s
knownGlobalRef = allGlobalRefs ! knownIndex


globalRefMap :: MapF CT.SymbolRepr GlobalRef
globalRefMap = MapF.fromList $
  FC.toListFC (\gb -> Pair (globalRefSymbol gb) gb) allGlobalRefs

ctxSizeRepr :: forall ctx. Size ctx -> NR.NatRepr (CtxSize ctx)
ctxSizeRepr sz = case viewSize sz of
  ZeroSize -> NR.knownNat
  IncSize sz' -> NR.addNat (NR.knownNat @1) (ctxSizeRepr sz')

-- | Index into the set of all tracked globals - pointing to the array that contains all of the GPRs
gprGlobalIndex :: Index StructGlobalsCtx AllGPRBaseType
gprGlobalIndex = knownIndex

-- | Index into the set of all tracked globals - pointing to the array that contains all of the SIMDs
simdGlobalIndex :: Index StructGlobalsCtx AllSIMDBaseType
simdGlobalIndex = knownIndex

testGlobalEq :: forall s s'
              . IsGlobal s
             => GlobalRef s'
             -> Maybe (s :~: s')
testGlobalEq gr = do
  Refl <- testEquality (knownGlobalRef @s) gr
  return Refl

globalRefSymbol :: GlobalRef s -> CT.SymbolRepr s
globalRefSymbol gr = case gr of
  SimpleGlobalRef ref -> withSimpleGlobalRef ref $ \symb -> symb
  GPRRef ref -> withGPRRef ref $ \n -> mkIndexedSymbol knownSymbol n
  SIMDRef ref -> withSIMDRef ref $ \n -> mkIndexedSymbol knownSymbol n
  MemoryRef -> CT.knownSymbol

globalRefIndex :: forall s. GlobalRef s -> Index GlobalsCtx (GlobalsType s)
globalRefIndex gr = withGlobalRef gr $
  mapContextIndex (Proxy @(GlobalsTypeWrapper))
    Ctx.knownSize (knownIndex @GlobalSymsCtx @s)

globalRefRepr :: forall s. GlobalRef s -> WI.BaseTypeRepr (GlobalsType s)
globalRefRepr gr =
  (knownRepr :: Assignment WI.BaseTypeRepr GlobalsCtx) ! globalRefIndex gr

globalOfGlobalRef :: GlobalRef s -> Global (GlobalsType s)
globalOfGlobalRef gr =
  flatTrackedGlobals ! globalRefIndex gr


instance OrdF GlobalRef where
  compareF gr1 gr2 = compareF (globalRefSymbol gr1) (globalRefSymbol gr2)

mkGlobalRef :: IsGlobal s => CT.SymbolRepr s -> GlobalRef s
mkGlobalRef _ = knownGlobalRef

lookupGlobalRefSymbol :: CT.SymbolRepr s -> Maybe (GlobalRef s)
lookupGlobalRefSymbol symb = MapF.lookup symb globalRefMap

lookupGlobalRef :: String -> Maybe (Some GlobalRef)
lookupGlobalRef str = case CT.someSymbol (T.pack str) of
  Some symb -> Some <$> lookupGlobalRefSymbol symb

lookupSimpleGlobalRef :: String -> Maybe (Some SimpleGlobalRef)
lookupSimpleGlobalRef str = case lookupGlobalRef str of
  Just (Some (SimpleGlobalRef sgr)) -> Just $ Some sgr
  _ -> Nothing


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
  , gpr13GRef <- knownGlobalRef @"_R13"
  , gpr13Ref' <- knownGPRRef @13
  , gpr13GRef' <- knownGPRGlobalRef @13
  , Nothing <- testEquality pcGref gpr13GRef
  , Just Refl <- testEquality $([e| knownGlobalRef @"_PC" |]) pcGref
  , Just Refl <- testEquality gpr13GRef (GPRRef gpr13Ref')
  , Just Refl <- testEquality gpr13GRef' gpr13GRef
  , simd25Ref <- knownGlobalRef @"_V25"
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
      gr' <- lookupGlobalRefSymbol (globalRefSymbol gr)
      Refl <- testEquality gr gr'
      case gr of
        SIMDRef simdRef -> withSIMDRef simdRef $ \n -> do
          gr'' <- lookupGlobalRefSymbol (mkIndexedSymbol (knownSymbol @"_V") n)
          Refl <- testEquality gr gr''
          Refl <- testEquality (mkSIMDRef n) simdRef
          Refl <- testEquality (mkSIMDGlobalRef n) gr
          return ()
        GPRRef gprRef -> withGPRRef gprRef $ \n -> do
          gr'' <- lookupGlobalRefSymbol (mkIndexedSymbol (knownSymbol @"_R") n)
          Refl <- testEquality gr gr''
          Refl <- testEquality (mkGPRRef n) gprRef
          Refl <- testEquality (mkGPRGlobalRef n) gr
          return ()
        _ -> return ()
