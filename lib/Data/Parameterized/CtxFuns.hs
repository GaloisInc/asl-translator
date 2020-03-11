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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}

-- Collection of type-level functions
module Data.Parameterized.CtxFuns
  ( CtxUpTo
  , NatToSymbol
  , IndexedSymbol
  , CtxReplicate
  , mkNatSymbol
  , mkAppendSymbol
  , mkIndexedSymbol
  , replicatedCtxPrf
  , natUpToIndex
  -- copied from SemMC
  , TyFun
  , Apply
  , MapCtx
  , applyMapCtx
  , traverseMapCtx
  , revApplyMapCtx
  , revTraverseMapCtx
  , mapCtxSize
  , mapCtxIndex
  , IndexApplied(..)
  , fromMapCtxSize
  , fromMapCtxIndex
  , PairF(..)
  , unzipPairF
  ) where

import           GHC.TypeLits
import           Unsafe.Coerce
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

import           Control.Applicative

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


testNatIndex :: forall maxn n m
              . Proxy maxn
             -> NR.NatRepr n
             -> Index (CtxUpTo maxn) m
             -> Maybe (n :~: m)
testNatIndex _ n idx = case (indexVal idx == (fromIntegral $ NR.intValue n)) of
  True -> Just (unsafeCoerce (Refl :: n :~: n))
  False -> Nothing

natUpToIndex :: forall n maxn
              . n <= maxn
             => Proxy maxn
             -> Size (CtxUpTo maxn)
             -> NR.NatRepr n
             -> Index (CtxUpTo maxn) n
natUpToIndex _ sz n
  | Just (Some idx) <- intIndex (fromIntegral $ NR.intValue n) sz
  , Just Refl <- testNatIndex (Proxy @maxn) n idx
  = idx
natUpToIndex _ _ _ = error $ "boundedNatUpToIndex: impossible"


type family CtxReplicate k (n :: Nat) where
  CtxReplicate k 0 = EmptyCtx
  CtxReplicate k n = CtxReplicate k (n - 1) ::> k

#ifdef UNSAFE_OPS
replicatedCtxPrf :: forall k n tp
                  . NR.NatRepr n
                 -> Size (CtxReplicate k n)
                 -> Index (CtxReplicate k n) tp
                 -> tp :~: k
replicatedCtxPrf n sz idx = unsafeCoerce (Refl :: tp :~: tp)
#else
_ctxReplicateStep :: forall k f n. f n -> CtxReplicate k (n + 1) :~: (CtxReplicate k n ::> k)
_ctxReplicateStep _ = unsafeCoerce (Refl :: CtxReplicate k n :~: CtxReplicate k n)

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
      | Refl <- _ctxReplicateStep @k (NR.decNat n)
      , Refl <- NR.minusPlusCancel n (NR.knownNat @1)
      -> case viewIndex sz idx of
           IndexViewLast sz' -> Refl
           IndexViewInit idx' -> replicatedCtxPrf (NR.decNat n) (decSize sz) idx'
#endif


-- Clagged from TyMap
data TyFun :: k1 -> k2 -> Type
type family Apply (f :: TyFun k1 k2 -> Type) (x :: k1) :: k2

type family MapCtx (f :: TyFun k1 k2 -> Type) (xs :: Ctx.Ctx k1) :: Ctx.Ctx k2 where
  MapCtx f Ctx.EmptyCtx = Ctx.EmptyCtx
  MapCtx f (xs Ctx.::> x) = MapCtx f xs Ctx.::> Apply f x

applyMapCtx :: forall (f :: TyFun k1 k2 -> Type) (xs :: Ctx.Ctx k1)
                 (g :: k2 -> Type) (h :: k1 -> Type)
               . Proxy f -> (forall (x :: k1). h x -> g (Apply f x))
              -> Ctx.Assignment h xs
              -> Ctx.Assignment g (MapCtx f xs)
applyMapCtx p1 f asn = case Ctx.viewAssign asn of
  Ctx.AssignEmpty -> Ctx.empty
  Ctx.AssignExtend asn' x -> applyMapCtx p1 f asn' Ctx.:> f x

traverseMapCtx :: forall (f :: TyFun k1 k2 -> Type) (xs :: Ctx.Ctx k1)
                  (g :: k2 -> Type) (h :: k1 -> Type) m
                . Applicative m
               => Proxy f -> (forall (x :: k1). h x -> m (g (Apply f x)))
               -> Ctx.Assignment h xs
               -> m (Ctx.Assignment g (MapCtx f xs))
traverseMapCtx p1 f asn = case Ctx.viewAssign asn of
  Ctx.AssignEmpty -> pure Ctx.empty
  Ctx.AssignExtend asn' x -> liftA2 (:>) (traverseMapCtx p1 f asn') (f x)

revApplyMapCtx :: forall (f :: TyFun k1 k2 -> Type) (xs :: Ctx k1)
                         (g :: k2 -> Type) (h :: k1 -> Type) w
                . Proxy f -> (forall (x :: k1). g (Apply f x) -> h x)
               -> Ctx.Assignment g (MapCtx f xs)
               -> Ctx.Assignment h xs
revApplyMapCtx p1 f Ctx.Empty | Refl <- zeroMapCtx p1 (Proxy @xs) = Ctx.empty
revApplyMapCtx p1 f (rest :> a) | ApplyRepr <- appliedMapCtx p1 (Proxy @xs) (viewCtxRepr (Ctx.size (rest :> a))) =
  revApplyMapCtx p1 f rest :> f a

revTraverseMapCtx :: forall (f :: TyFun k1 k2 -> Type) (xs :: Ctx k1)
                            (g :: k2 -> Type) (h :: k1 -> Type) m
                   . Applicative m
                  => Proxy f -> (forall (x :: k1). g (Apply f x) -> m (h x))
                  -> Ctx.Assignment g (MapCtx f xs)
                  -> m (Ctx.Assignment h xs)
revTraverseMapCtx p1 f Ctx.Empty | Refl <- zeroMapCtx p1 (Proxy @xs) = pure $ Ctx.empty
revTraverseMapCtx p1 f (rest :> a)
  | ApplyRepr <- appliedMapCtx p1 (Proxy @xs) (viewCtxRepr (Ctx.size (rest :> a))) =
    liftA2 (:>) (revTraverseMapCtx p1 f rest) (f a)

-- fin

data ViewCtxRepr ctx tp where
  ViewCtxRepr :: ViewCtxRepr (ctx ::> tp) tp

data ApplyRepr f ctx tp where
  ApplyRepr :: ApplyRepr f (ctx ::> tp) (Apply f tp)

zeroMapCtx :: (MapCtx f ctx) ~ EmptyCtx => Proxy f -> Proxy ctx -> ctx :~: EmptyCtx
zeroMapCtx _ _ = unsafeCoerce (Refl :: EmptyCtx :~: EmptyCtx)

appliedMapCtx :: Proxy f
              -> Proxy ctx
              -> ViewCtxRepr (MapCtx f ctx) tp
              -> ApplyRepr f ctx tp
appliedMapCtx _ _  ViewCtxRepr = unsafeCoerce (ApplyRepr)


viewCtxRepr :: Size (ctx ::> tp) -> ViewCtxRepr (ctx ::> tp) tp
viewCtxRepr _ = ViewCtxRepr

headTailProxies :: forall ctx tp. Proxy (ctx ::> tp) -> (Proxy ctx, Proxy tp)
headTailProxies _ = (Proxy @ctx, Proxy @tp)


-- | Witness that an index into a mapped context is the result of some 'Apply'
data IndexApplied f ctx tp where
  IndexApplied :: Proxy f -> Ctx.Index ctx tp -> IndexApplied f ctx (Apply f tp)

fromMapCtxIndex :: forall f ctx tp
                 . Proxy f
                -> Proxy ctx
                -> Size (MapCtx f ctx)
                -> Index (MapCtx f ctx) tp
                -> IndexApplied f ctx tp
fromMapCtxIndex f ctx sz idx = case viewIndex sz idx of
  IndexViewLast sz'
    |  ApplyRepr <- appliedMapCtx f ctx (viewCtxRepr sz)
    -> IndexApplied f $ lastIndex (fromMapCtxSize f ctx sz)
  IndexViewInit idx'
    | ApplyRepr <- appliedMapCtx f ctx (viewCtxRepr sz)
    , (ctx', _) <- headTailProxies (Proxy @ctx)
    -> case fromMapCtxIndex f ctx' (decSize sz) idx' of
        IndexApplied _ idx'' -> IndexApplied f (skipIndex idx'')

-- the mapped context has the same size/shape, so indexes and sizes
-- are portable between them.
#ifdef UNSAFE_OPS
mapCtxSize :: Proxy f
               -> Size ctx
               -> Size (MapCtx f ctx)
mapCtxSize _ sz = unsafeCoerce sz

mapCtxIndex :: Proxy f
                -> Size ctx
                -> Index ctx tp
                -> Index (MapCtx f ctx) (Apply f tp)
mapCtxIndex _ _ idx = unsafeCoerce idx

fromMapCtxSize :: forall f ctx
                . Proxy f
               -> Proxy ctx
               -> Size (MapCtx f ctx)
               -> Size ctx
fromMapCtxSize _ _ sz = unsafeCoerce sz


#else
mapCtxSize :: Proxy f
               -> Size ctx
               -> Size (MapCtx f ctx)
mapCtxSize pf sz = case viewSize sz of
  ZeroSize -> zeroSize
  IncSize sz' -> incSize (mapCtxSize pf sz')

mapCtxIndex :: Proxy f
                -> Size ctx
                -> Index ctx tp
                -> Index (MapCtx f ctx) (Apply f tp)
mapCtxIndex pf sz idx = case viewIndex sz idx of
  IndexViewLast sz' -> lastIndex (mapCtxSize pf sz)
  IndexViewInit idx' -> skipIndex (mapCtxIndex pf (decSize sz) idx')

fromMapCtxSize :: forall f ctx
                . Proxy f
               -> Proxy ctx
               -> Size (MapCtx f ctx)
               -> Size ctx
fromMapCtxSize f ctx sz = case viewSize sz of
  ZeroSize | Refl <- zeroMapCtx f ctx -> zeroSize
  IncSize sz'
   | ApplyRepr <- appliedMapCtx f ctx (viewCtxRepr sz)
   , (ctx', _) <- headTailProxies ctx
   -> incSize $ fromMapCtxSize f ctx' sz'
#endif

data PairF (t1 :: k -> *) (t2 :: k -> *) (t :: k) where
  PairF :: !(a t) -> !(b t) -> PairF a b t

unzipPairF :: Ctx.Assignment (PairF a b) ctx -> (Ctx.Assignment a ctx, Ctx.Assignment b ctx)
unzipPairF asn = case Ctx.viewAssign asn of
  Ctx.AssignEmpty -> (Ctx.empty, Ctx.empty)
  Ctx.AssignExtend asn' (PairF a b) ->
    let
      (asna, asnb) = unzipPairF asn'
    in (asna Ctx.:> a, asnb Ctx.:> b)

-- instance (KnownRepr t1 e1, KnownRepr t2 e2) => KnownRepr (PairF t1 t2) '(e1, e2) where
--   knownRepr = PairF knownRepr knownRepr

-- type family Fst k :: a where
--   Fst '(a, b) = a

-- type family Snd k :: b where
--   Snd '(a, b) = b

-- data FstWrapper :: TyFun (a, b) a -> Type

-- type instance Apply FstWrapper k = Fst k

-- data SndWrapper :: TyFun (a, b) b -> Type

-- type instance Apply SndWrapper k = Snd k
