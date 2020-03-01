{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- Collection of type-level functions
module Data.Parameterized.CtxFuns
  ( CtxUpTo
  , NatToSymbol
  , IndexedSymbol
  , CtxReplicate
  , GeqProofRepr(..)
  , withGeqProofRepr
  , mkNatSymbol
  , mkAppendSymbol
  , mkIndexedSymbol
  , upToProofRepr
  , replicatedAsnPrf
  -- copied from SemMC
  , TyFun
  , Apply
  , MapContext
  , mapContextSize
  , mapContextIndex
  ) where

import           GHC.TypeLits
import           Unsafe.Coerce
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

import           Data.Maybe ( fromJust )
import           Data.Proxy
import           Data.Kind
import           Data.Void
import qualified Data.Text as T

import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.SymbolRepr

-- "printing" type-level nats into type-level symbols

-- type family NatToSymbol (n :: Nat) :: Symbol
$(do
    natToSymbol <- return $ TH.mkName "NatToSymbol"
    n <- return $ TH.mkName "n"
    natK <- [t| Nat |]
    symbK <- [t| Symbol |]
    tyHead <- return $ TH.TypeFamilyHead natToSymbol [TH.KindedTV n natK] (TH.KindSig symbK) Nothing
    let mkSyn i = TH.TySynEqn [TH.LitT (TH.NumTyLit i)] (TH.LitT $ TH.StrTyLit (show i))
    return $ [TH.ClosedTypeFamilyD tyHead (map mkSyn [0..31])]
 )

type IndexedSymbol (s :: Symbol) (n :: Nat) = AppendSymbol s (NatToSymbol n)

mkNatSymbol :: NR.NatRepr n -> SymbolRepr (NatToSymbol n)
mkNatSymbol nr = case someSymbol (T.pack (show (NR.natValue nr))) of
  Some symb -> unsafeCoerce symb

mkAppendSymbol :: SymbolRepr s -> SymbolRepr s' -> SymbolRepr (AppendSymbol s s')
mkAppendSymbol s s' = case someSymbol (symbolRepr s <> symbolRepr s') of
  Some symb -> unsafeCoerce symb

mkIndexedSymbol :: SymbolRepr s -> NR.NatRepr n -> SymbolRepr (IndexedSymbol s n)
mkIndexedSymbol s n = mkAppendSymbol s (mkNatSymbol n)

type family CtxUpTo (n :: Nat) :: Ctx Nat where
  CtxUpTo 0 = EmptyCtx ::> 0
  CtxUpTo n = CtxUpTo (n - 1) ::> n


-- Helper type to make this proof work.
data AssignmentUpTo f (n :: Nat) where
  AssignmentUpToZero :: f 0 -> AssignmentUpTo f 0
  AssignmentUpToRest :: AssignmentUpTo f n -> f (n + 1) -> AssignmentUpTo f (n + 1)

upToProofReprStep :: GeqProofRepr n m -> AssignmentUpTo (GeqProofRepr n) m
upToProofReprStep (GeqProofRepr n m) = case NR.isZeroOrGT1 m of
  Left Refl -> AssignmentUpToZero $ GeqProofRepr n m
  Right NR.LeqProof
   | NR.LeqProof <- NR.leqSub (NR.leqProof m n) (NR.leqProof (NR.knownNat @1) m)
   , asn <- upToProofReprStep (GeqProofRepr n (NR.decNat m))
   , Refl <- NR.minusPlusCancel m (NR.knownNat @1)
   -> AssignmentUpToRest asn $ GeqProofRepr n m

upToProofRepr' :: NR.NatRepr n -> AssignmentUpTo (GeqProofRepr n) n
upToProofRepr' n = upToProofReprStep (GeqProofRepr n n)

assignmentFromUpTo :: AssignmentUpTo f n -> Assignment f (CtxUpTo n)
assignmentFromUpTo asn = case asn of
  AssignmentUpToZero a -> Ctx.empty :> a
  AssignmentUpToRest asnUT a | Refl <- ctxUpToStep asnUT -> assignmentFromUpTo asnUT :> a

-- | The main result: an 'Assignment' of proofs about the consistency of each element.
upToProofRepr :: NR.NatRepr n -> Assignment (GeqProofRepr n) (CtxUpTo n)
upToProofRepr n = assignmentFromUpTo (upToProofRepr' n)

-- FIXME: I'm not sure why this isn't provable.
ctxUpToStep :: f n -> CtxUpTo (n + 1) :~: (CtxUpTo n ::> (n + 1))
ctxUpToStep _ = unsafeCoerce (Refl :: CtxUpTo n :~: CtxUpTo n)

type family CtxReplicate k (n :: Nat) where
  CtxReplicate k 0 = EmptyCtx
  CtxReplicate k n = CtxReplicate k (n - 1) ::> k

ctxReplicateStep :: forall k f n. f n -> CtxReplicate k (n + 1) :~: (CtxReplicate k n ::> k)
ctxReplicateStep _ = unsafeCoerce (Refl :: CtxReplicate k n :~: CtxReplicate k n)

noEmptyIndex :: Index EmptyCtx tp -> Void
noEmptyIndex = error "impossible"

replicatedCtxPrf :: forall k n tp
                  . NR.NatRepr n
                 -> Size (CtxReplicate k n)
                 -> Index (CtxReplicate k n) tp
                 -> tp :~: k
replicatedCtxPrf n sz idx =
  case NR.isZeroOrGT1 n of
    Left Refl -> absurd $ noEmptyIndex idx
    Right NR.LeqProof
      | Refl <- ctxReplicateStep @k (NR.decNat n)
      , Refl <- NR.minusPlusCancel n (NR.knownNat @1)
      -> case viewIndex sz idx of
           IndexViewLast sz' -> Refl
           IndexViewInit idx' -> replicatedCtxPrf (NR.decNat n) (decSize sz) idx'


data GeqProofRepr (maxn :: Nat) (n :: Nat)  where
  GeqProofRepr :: forall maxn n. (n <= maxn) => NR.NatRepr maxn -> NR.NatRepr n -> GeqProofRepr maxn n

deriving instance Show (GeqProofRepr maxn n)
deriving instance Eq (GeqProofRepr maxn n)

instance ShowF (GeqProofRepr maxn) where
  showF vnr = show vnr

instance TestEquality (GeqProofRepr maxn) where
  testEquality (GeqProofRepr _ nr) (GeqProofRepr _ nr') = testEquality nr nr'

instance OrdF (GeqProofRepr maxn) where
  compareF (GeqProofRepr _ nr) (GeqProofRepr _ nr') = compareF nr nr'

withGeqProofRepr :: forall n maxn a
                  . GeqProofRepr maxn n
                 -> (n <= maxn => NR.LeqProof n maxn -> NR.NatRepr maxn -> NR.NatRepr n -> a)
                 -> a
withGeqProofRepr (GeqProofRepr maxn n) f = f (NR.leqProof n maxn) maxn n


boundedNatToIndex :: forall ctx n
                   . Size ctx
                  -> GeqProofRepr (CtxSize ctx - 1) n
                  -> Some (Index ctx)
boundedNatToIndex sz (GeqProofRepr _ nr) = fromJust $ intIndex (fromIntegral $ NR.natValue nr) sz

-- Clagged from TyMap
data TyFun :: k1 -> k2 -> Type
type family Apply (f :: TyFun k1 k2 -> Type) (x :: k1) :: k2

type family MapContext (f :: TyFun k1 k2 -> Type) (xs :: Ctx.Ctx k1) :: Ctx.Ctx k2 where
  MapContext f Ctx.EmptyCtx = Ctx.EmptyCtx
  MapContext f (xs Ctx.::> x) = MapContext f xs Ctx.::> Apply f x
-- fin

-- proofs about maps
mapContextSize :: Proxy f -> Size ctx -> Size (MapContext f ctx)
mapContextSize pf sz = case viewSize sz of
  ZeroSize -> zeroSize
  IncSize sz' -> incSize (mapContextSize pf sz')

mapContextIndex :: Proxy f -> Size ctx -> Index ctx tp -> Index (MapContext f ctx) (Apply f tp)
mapContextIndex pf sz idx = case viewIndex sz idx of
  IndexViewLast sz' -> lastIndex (mapContextSize pf sz)
  IndexViewInit idx' -> skipIndex (mapContextIndex pf (decSize sz) idx')
--
