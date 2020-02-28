{-# LANGUAGE GADTs #-}
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
{-# LANGUAGE CPP #-}

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
  , GlobalRef
  , GlobalSymsCtx
  , lookupGlobalRef
  , knownGlobalIndex
  , knownIndexedGlobalRef
  , knownGlobalRef
  , knownGPRRef
  , knownSIMDRef
  , globalRefSymbol
  , globalRefRepr
  , globalRefIndex
  , testGlobalEq
  , allGlobalRefs
  , unGR
  )

where

import           GHC.TypeLits

import           Control.Applicative ( Const(..) )
import           Control.Monad.Identity
import qualified Control.Monad.Except as ME

import qualified Data.Text as T
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes )

import           Data.Parameterized.Context
import           Data.Parameterized.Some ( Some(..) )
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

#ifdef UNSAFE_OPS
import           Unsafe.Coerce
#endif

type UntrackedGlobalsCtx = $(mkTypeFromGlobals untrackedGlobals')
type GlobalsCtx = $(mkTypeFromGlobals trackedGlobals')

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
             . Assignment (LabeledValue T.Text WI.BaseTypeRepr) globals
            -> MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index globals)
mkMapIndexF reprs = runIdentity $ do
  pairs <- traverseWithIndex mkEntry reprs
  return $ MapF.fromList $ FC.toListFC (\(Const c) -> c) pairs
  where
    mkEntry :: Index globals tp
            -> LabeledValue T.Text WI.BaseTypeRepr tp
            -> Identity (Const (Pair (LabeledValue T.Text WI.BaseTypeRepr) (Index globals)) tp)
    mkEntry idx lbl = return $ Const $ Pair lbl idx

globalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index GlobalsCtx)
globalsMapIndexF = mkMapIndexF trackedGlobalReprs

untrackedGlobalsMapIndexF :: MapF (LabeledValue T.Text WI.BaseTypeRepr) (Index UntrackedGlobalsCtx)
untrackedGlobalsMapIndexF = mkMapIndexF untrackedGlobalReprs

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

$(mkInstDeclsFromGlobals trackedGlobals')

type GlobalSymsCtx = $(mkAllGlobalSymsT trackedGlobals')

globalsSyms :: MapF CT.SymbolRepr (SGlobal GlobalsCtx)
globalsSyms = MapF.fromList $ ($(mkGlobalsSyms trackedGlobals') globalsMapIndexF)

data GlobalRef (s :: Symbol) where
  GlobalRef :: CT.SymbolRepr s -> Index GlobalsCtx (GlobalsType s) -> GlobalRef s

testGlobalEq :: forall s s'
              . IsGlobal s
             => GlobalRef s'
             -> Maybe (s :~: s')
testGlobalEq gr = do
  Refl <- testEquality (knownGlobalRef @s) gr
  return Refl

unGR :: GlobalRef s -> (CT.SymbolRepr s, WI.BaseTypeRepr (GlobalsType s), Index GlobalsCtx (GlobalsType s))
unGR (GlobalRef repr idx) = (repr, trackedGlobalBaseReprs ! idx, idx)

globalRefSymbol :: GlobalRef s -> CT.SymbolRepr s
globalRefSymbol gr = case unGR gr of (s, _, _) -> s

globalRefRepr :: GlobalRef s -> WI.BaseTypeRepr (GlobalsType s)
globalRefRepr gr = case unGR gr of (_, repr, _) -> repr

globalRefIndex :: GlobalRef s -> Index GlobalsCtx (GlobalsType s)
globalRefIndex gr = case unGR gr of (_, _, idx) -> idx

-- Here we explicitly assume that each symbol represents a unique global ref
instance TestEquality GlobalRef where
  testEquality gr1 gr2 = case (unGR gr1, unGR gr2) of
    ((s1, _, _), (s2, _, _)) -> testEquality s1 s2

instance OrdF GlobalRef where
  compareF gr1 gr2 = case (unGR gr1, unGR gr2) of
    ((s1, _, _), (s2, _, _)) -> compareF s1 s2

knownSGlobal :: forall s
            . IsGlobal s
           => SGlobal GlobalsCtx s
knownSGlobal =
  let repr = CT.knownSymbol :: CT.SymbolRepr s
  in case MapF.lookup repr globalsSyms of
    Just (SGlobal r) -> SGlobal r
    Nothing -> error $ "No corresponding global for: " ++ show repr

lookupGlobalRef :: String -> Maybe (Some GlobalRef)
lookupGlobalRef str = case CT.someSymbol (T.pack str) of
  Some symb -> case MapF.lookup symb globalsSyms of
    Just (SGlobal idx) -> Just $ Some $ GlobalRef symb idx
    _ -> Nothing

knownIndexedGlobalRef :: forall s n. IsGlobal (IndexedSymbol s n) => GlobalRef (IndexedSymbol s n)
knownIndexedGlobalRef = knownGlobalRef

-- It isn't clear how to efficiently turn a range constraint (n <= 14) into
-- a known symbol-equivalent. The 'forNats' function here simply explodes out
-- all possibilities for the given NatRepr, which ends up doing n case analyses.

knownGPRRef' :: forall n. n <= 14 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_R" n)
knownGPRRef' = $(forNats 14 [e| knownGlobalRef |])

knownSIMDRef' :: forall n. n <= 31 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_V" n)
knownSIMDRef' = $(forNats 31 [e| knownGlobalRef |])


-- For the unsafe equivalent, we can simply do a value-level string append and
-- assert that the result is expected. We typecheck the safe implementation regardless
-- to add some guard rails to this.

#ifdef UNSAFE_OPS
knownGPRRef :: forall n. n <= 14 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_R" n)
knownGPRRef nr = case lookupGlobalRef ("_R" ++ show (NR.intValue nr)) of
  Just (Some gr) -> unsafeCoerce gr
  Nothing -> error "knownGPRRef: unsafe lookup failed"

knownSIMDRef :: forall n. n <= 31 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_V" n)
knownSIMDRef nr = case lookupGlobalRef ("_V"  ++ show (NR.intValue nr)) of
  Just (Some gr) -> unsafeCoerce gr
  Nothing -> error "knownSIMDRef: unsafe lookup failed"
#else
knownGPRRef :: forall n. n <= 14 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_R" n)
knownGPRRef = knownGPRRef'

knownSIMDRef :: forall n. n <= 31 => NR.NatRepr n -> GlobalRef (IndexedSymbol "_V" n)
knownSIMDRef = knownSIMDRef'
#endif

knownGlobalIndex :: forall s
                  . IsGlobal s
                 => Index GlobalsCtx (GlobalsType s)
knownGlobalIndex = unSG @GlobalsCtx @s $ knownSGlobal

knownGlobalRef :: forall s
                . IsGlobal s
               => GlobalRef s
knownGlobalRef = case knownSGlobal @s of
  SGlobal r -> GlobalRef CT.knownSymbol r

instance TH.Lift (GlobalRef s) where
  lift gr = [e| knownGlobalRef :: GlobalRef $(TH.litT (TH.strTyLit (T.unpack $ CT.symbolRepr $ globalRefSymbol gr))) |]

-- | This is a little bit gross, since we need to establish IsGlobal for each element.
allGlobalRefs :: Assignment GlobalRef GlobalSymsCtx
allGlobalRefs = $(foldGlobals trackedGlobals'
                  (TH.lamE [return TH.WildP, return TH.WildP] (TH.varE (TH.mkName "knownGlobalRef")))
                 [e| (:>) |] [| empty |])

_test :: Index GlobalsCtx (GlobalsType "_PC")
_test = knownGlobalIndex @"_PC"

_testLift :: GlobalRef "_PC"
_testLift = $([e| knownGlobalRef @"_PC" |])
