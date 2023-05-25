{-|
Module           : Data.Parameterized.AssignTree
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Generalization of Assignments over type-level trees

-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}


module Data.Parameterized.AssignTree
  ( type CtxTree(..)
  , CtxLeaf
  , CtxBranch
  , AssignTree(..)
  , FlattenCtxTrees
  , FlattenCtxTree
  , MapCtxTree
  , CollapseCtxTree
  , zipWithM
  , flattenAsnTrees
  , flattenAsnTree
  , collapseAssignTree
  , collapseUnflatten
  , traverseMapCtxTree
  , revTraverseMapCtxTree
  ) where

import           Unsafe.Coerce
import           Data.Proxy
import           Data.Kind
import           Control.Monad.Identity hiding (zipWithM)

import           Data.Parameterized.Context hiding (zipWithM)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.CtxFuns
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Classes

-- | A tree of 'Ctx's
data CtxTree k
  = CtxLeaf k
  | CtxBranch (Ctx (CtxTree k))

type CtxLeaf (tp :: k) = 'CtxLeaf tp
type CtxBranch (c :: Ctx (CtxTree k)) = 'CtxBranch c

-- | A tree of 'Assignment's
data AssignTree (f :: k -> Type) (tp :: CtxTree k) where
  AssignTreeLeaf :: f tp -> AssignTree f (CtxLeaf tp)
  AssignTreeBranch :: Assignment (AssignTree f) ctx -> AssignTree f (CtxBranch ctx)

zipWithM :: Applicative m
         => (forall tp. a tp -> b tp -> m (c tp))
         -> AssignTree a ctxts
         -> AssignTree b ctxts
         -> m (AssignTree c ctxts)
zipWithM f a b = case (a, b) of
  (AssignTreeLeaf a', AssignTreeLeaf b') -> AssignTreeLeaf <$> f a' b'
  (AssignTreeBranch as, AssignTreeBranch bs) -> AssignTreeBranch <$> Ctx.zipWithM (zipWithM f) as bs

zipPairF :: AssignTree a ctxts -> AssignTree b ctxts -> AssignTree (PairF a b) ctxts
zipPairF a b = case (a, b) of
  (AssignTreeLeaf a', AssignTreeLeaf b') -> AssignTreeLeaf $ PairF a' b'
  (AssignTreeBranch as, AssignTreeBranch bs) -> AssignTreeBranch $ Ctx.zipWith zipPairF as bs

traverseAssignTree :: Applicative m
                   => (forall tp'. f tp' -> m (g tp'))
                   -> AssignTree f tp
                   -> m (AssignTree g tp)
traverseAssignTree f tree = case tree of
  AssignTreeLeaf e -> AssignTreeLeaf <$> f e
  AssignTreeBranch trees -> AssignTreeBranch <$> FC.traverseFC (traverseAssignTree f) trees

instance FC.FunctorFC AssignTree where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC AssignTree where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC AssignTree where
  traverseFC f = traverseAssignTree f


type family FlattenCtxTrees (trees :: Ctx (CtxTree k)) :: Ctx k where
  FlattenCtxTrees (ctx ::> k) = FlattenCtxTrees ctx <+> FlattenCtxTree k
  FlattenCtxTrees EmptyCtx = EmptyCtx

-- | Flatten a 'CtxTree' into a 'Ctx' via a leftmost traversal
type family FlattenCtxTree (ctx :: CtxTree k) :: Ctx k where
  FlattenCtxTree ('CtxLeaf k) = EmptyCtx ::> k
  FlattenCtxTree ('CtxBranch trees) = FlattenCtxTrees trees

flattenAsnTrees :: Assignment (AssignTree f) ctx
                -> Assignment f (FlattenCtxTrees ctx)
flattenAsnTrees trees = case viewAssign trees of
  AssignExtend trees' t -> case t of
    AssignTreeBranch trees'' -> flattenAsnTrees trees' <++> flattenAsnTrees trees''
    AssignTreeLeaf e -> flattenAsnTrees trees' :> e
  AssignEmpty -> empty

-- | Flatten an 'AssignTree' into an 'Assignment' via a leftmost traversal
flattenAsnTree :: AssignTree f ctx -> Assignment f (FlattenCtxTree ctx)
flattenAsnTree tree = case tree of
  AssignTreeBranch trees -> flattenAsnTrees trees
  AssignTreeLeaf e -> singleton e

assignTreeIndexes :: forall f ctx
                   . Assignment (AssignTree f) ctx
                  -> Assignment (AssignTree (Index (FlattenCtxTrees ctx))) ctx
assignTreeIndexes trees = case viewAssign trees of
  AssignExtend (trees' :: Assignment (AssignTree f) ctx')  tree ->
    let
      left = assignTreeIndexes trees'
      left_flat = flattenAsnTrees trees'
    in case tree of
      AssignTreeBranch trees'' ->
        let
          right = assignTreeIndexes trees''
          right_flat = flattenAsnTrees trees''

          lembed = appendEmbedding (size left_flat) (size right_flat)
          left1 = FC.fmapFC (FC.fmapFC (applyEmbedding' lembed)) left

          rembed = appendEmbeddingLeft (size left_flat) (size right_flat)
          right1 = FC.fmapFC (FC.fmapFC (applyEmbedding' rembed)) right
        in left1 :> AssignTreeBranch right1
      AssignTreeLeaf (_ :: f tp) ->
        let
          lindex :: forall tp'. Index (FlattenCtxTrees ctx') tp'
                 -> Index (FlattenCtxTrees ctx' ::> tp) tp'
          lindex = skipIndex
          left1 = FC.fmapFC (FC.fmapFC lindex) left
        in left1 :> AssignTreeLeaf (nextIndex (size left_flat))
  AssignEmpty -> empty

assignTreeIndex :: forall f ctxts
                 . AssignTree f ctxts
                -> AssignTree (Index (FlattenCtxTree ctxts)) ctxts
assignTreeIndex tree = case tree of
  AssignTreeLeaf _ -> AssignTreeLeaf (nextIndex zeroSize)
  AssignTreeBranch trees -> AssignTreeBranch (assignTreeIndexes trees)

-- | Collapse a 'CtxTree' by recursively applying the given function to its leaves
type family CollapseCtxTree (f :: TyFun (Ctx k) k -> Type) (ctxt :: CtxTree k) :: k where
  CollapseCtxTree f ('CtxLeaf k) = k
  CollapseCtxTree f ('CtxBranch ctxts) = Apply f (MapCtx (CollapseCtxTreeWrapper f) ctxts)

data CollapseCtxTreeWrapper :: (TyFun (Ctx k) k -> Type) -> TyFun (CtxTree k) k -> Type
type instance Apply (CollapseCtxTreeWrapper f) t = CollapseCtxTree f t

-- | Collapse an 'AssignTree' by recursively applying the given collapsing function to its leaves
collapseAssignTree :: forall k (h :: TyFun (Ctx k) k -> Type) m (ctxt :: CtxTree k) f g
                    . Monad m
                   => Proxy h
                   -> (forall (tp' :: k). f tp' -> m (g tp'))
                   -> (forall ctx. Assignment g ctx -> m (g (Apply h ctx)))
                   -> AssignTree f ctxt
                   -> m (g (CollapseCtxTree h ctxt))
collapseAssignTree ph g f tree = case tree of
  AssignTreeLeaf a -> g a
  AssignTreeBranch trees -> do
    trees' <- traverseMapCtx (Proxy @(CollapseCtxTreeWrapper h)) (collapseAssignTree ph g f) trees
    f trees'

data Applied g f tp where
  Applied :: g (Apply f tp) -> Applied g f tp

appliedTree :: Proxy f
            -> AssignTree g (MapCtxTree f xs)
            -> AssignTree (Applied g f) xs
appliedTree pf tree =
  runIdentity $ revTraverseMapCtxTree pf (\x -> return $ Applied x) tree

-- | Collapse a pair of 'AssignTree's, where one is the result of a type-level map.
collapseUnflatten :: forall k
                        (h :: TyFun (Ctx k) k -> Type)
                        (j :: TyFun k k -> Type)
                               m (ctxt :: CtxTree k) f g l
                     . Monad m
                    => Proxy h
                    -> Proxy j
                    -> (forall tp'. Index (FlattenCtxTree (MapCtxTree j ctxt)) (Apply j tp') -> l tp' -> f (Apply j tp') -> m (g tp'))
                    -> (forall ctx. Assignment g ctx -> m (g (Apply h ctx)))
                    -> AssignTree l ctxt
                    -> AssignTree f (MapCtxTree j ctxt)
                    -> m (g (CollapseCtxTree h ctxt))
collapseUnflatten ph pj g f tree revTree =
  let
    appTree = appliedTree pj revTree
    idxTree = appliedTree pj (assignTreeIndex revTree)
    ttree = zipPairF appTree (zipPairF idxTree tree)
  in collapseAssignTree ph (\(PairF (Applied f_j_tp) (PairF (Applied idx_j_tp) l_tp)) -> g idx_j_tp l_tp f_j_tp) f ttree


-- | Map the given type-level function over a 'CtxTree'
type family MapCtxTree (f :: TyFun k1 k2 -> Type) (xs :: CtxTree k1) :: CtxTree k2 where
  MapCtxTree f (CtxLeaf k) = 'CtxLeaf (Apply f k)
  MapCtxTree f (CtxBranch ctx) = 'CtxBranch (MapCtx (MapCtxTreeWrapper f) ctx)


data RevApply f tp where
  RevApply :: Proxy tp -> RevApply f (Apply f tp)

appliedLeaf :: MapCtxTree f ctx ~ CtxLeaf k => Proxy f -> Proxy ctx -> Proxy k -> RevApply f k
appliedLeaf _ _ _ = unsafeCoerce (RevApply Proxy)

appliedBranch :: MapCtxTree f ctx ~ CtxBranch ctxs => Proxy f -> Proxy ctx -> Proxy ctxs -> RevApply (MapCtxWrapper (MapCtxTreeWrapper f)) ctxs
appliedBranch _ _ _ = unsafeCoerce (RevApply Proxy)

mapCtxTreeLeafInject :: (MapCtxTree f ctxt) ~ CtxLeaf k => Apply f x ~ k => Proxy f -> Proxy ctxt -> Proxy k -> Proxy x -> ctxt :~: ('CtxLeaf x)
mapCtxTreeLeafInject _ _ _ _ = unsafeCoerce Refl

mapCtxTreeBranchInject :: (MapCtxTree f ctxt) ~ CtxBranch ctxts' => MapCtx (MapCtxTreeWrapper f) ctxts ~ ctxts' => Proxy f -> Proxy ctxt -> Proxy ctxts' -> Proxy ctxts -> ctxt :~: ('CtxBranch ctxts)
mapCtxTreeBranchInject _ _ _ _ = unsafeCoerce Refl

-- | Lift the 'MapCtxTree' type family to a 'TyFun'
data MapCtxTreeWrapper :: (TyFun k1 k2 -> Type) -> TyFun (CtxTree k1) (CtxTree k2) -> Type
type instance Apply (MapCtxTreeWrapper f) t = MapCtxTree f t

-- | Traverse an 'AssignTree' with a type-changing function
traverseMapCtxTree :: forall k1 k2 (f :: TyFun k1 k2 -> Type) (xs :: CtxTree k1)
                  (g :: k2 -> Type) (h :: k1 -> Type) m
                . Applicative m
               => Proxy f -> (forall (x :: k1). h x -> m (g (Apply f x)))
               -> AssignTree h xs
               -> m (AssignTree g (MapCtxTree f xs))
traverseMapCtxTree p1 f asn = case asn of
  AssignTreeLeaf e -> AssignTreeLeaf <$> f e
  AssignTreeBranch trees -> AssignTreeBranch <$> traverseMapCtx (Proxy :: Proxy (MapCtxTreeWrapper f)) (traverseMapCtxTree p1 f) trees

-- | Traverse an 'AssignTree' that was the result of some 'traverseMapCtxTree' and recover
-- the original type.
revTraverseMapCtxTree :: forall k1 k2 (f :: TyFun k1 k2 -> Type) (xs :: CtxTree k1)
                                (g :: k2 -> Type) (h :: k1 -> Type) m
                       . Applicative m
                      => Proxy f -> (forall (x :: k1). g (Apply f x) -> m (h x))
                      -> AssignTree g (MapCtxTree f xs)
                      -> m (AssignTree h xs)
revTraverseMapCtxTree p1 f tree = case tree of
  AssignTreeLeaf (e :: g tp)
    | RevApply x <- appliedLeaf p1 (Proxy @xs) (Proxy @tp)
    , Refl <- mapCtxTreeLeafInject p1 (Proxy @xs) (Proxy @tp) x
    -> AssignTreeLeaf <$> f e
  AssignTreeBranch (trees :: Assignment (AssignTree g) ctx)
    | RevApply x <- appliedBranch p1 (Proxy @xs) (Proxy @ctx)
    , Refl <- mapCtxTreeBranchInject p1 (Proxy @xs) (Proxy @ctx) x
    -> AssignTreeBranch <$> revTraverseMapCtx (Proxy :: Proxy (MapCtxTreeWrapper f)) (revTraverseMapCtxTree p1 f) trees
