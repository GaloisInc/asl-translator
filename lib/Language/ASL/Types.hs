{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Functions for converting between What4 and Crucible types.
module Language.ASL.Types
  ( ToBaseType
  , ToBaseTypes
  , ToBaseTypesList
  , CtxToList
  , ToCrucTypes
  , ConstVal(..)
  , UserType(..)
  , LabeledValue(..)
  , UserStructAcc
  , StructAccessor(..)
  , RegisterSig
  , ExtendedTypeData(..)
  , TypeConstraint(..)
  , ConstraintHint(..)
  , RegisterKind(..)
  , AccessMode(..)
  , assignmentToList
  , userTypeRepr
  , toBaseType
  , toBaseTypes
  , toCrucTypes
  , baseCrucProof
  , toFromBaseProof
  , fromBaseIndex
  , toBaseIndex
  , projectLabel
  , projectValue
  , addLabels
  , letInStmt
  , unletInStmt
  , blockStmt
  , unblockStmt
  , falseExpr
  , trueExpr
  ) where


import           Data.Kind ( Type )
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Text as T
import qualified Lang.Crucible.Types as CT
import What4.BaseTypes as WT
import           Data.Parameterized.Classes
import qualified Data.BitVector.Sized as BV
import qualified Language.ASL.Syntax as AS
import qualified Data.Map as Map


type family ToBaseType (ctp :: CT.CrucibleType) :: WT.BaseType where
  ToBaseType (CT.BaseToType bt) = bt

type family ToBaseTypes (ctps :: CT.Ctx CT.CrucibleType) :: CT.Ctx WT.BaseType where
  ToBaseTypes CT.EmptyCtx = CT.EmptyCtx
  ToBaseTypes (tps CT.::> tp) = ToBaseTypes tps CT.::> ToBaseType tp

toBaseType :: CT.TypeRepr ctp -> WT.BaseTypeRepr (ToBaseType ctp)
toBaseType repr = case CT.asBaseType repr of
  CT.NotBaseType -> error "Illegal crucible type"
  CT.AsBaseType brepr -> brepr

toBaseTypes :: Ctx.Assignment CT.TypeRepr ctps -> Ctx.Assignment WT.BaseTypeRepr (ToBaseTypes ctps)
toBaseTypes Ctx.Empty = Ctx.Empty
toBaseTypes (reprs Ctx.:> repr) = toBaseTypes reprs Ctx.:> toBaseType repr

-- type family ToCrucibleTypes (wtps :: CT.Ctx WT.BaseType) :: CT.Ctx CT.CrucibleType where
--   ToCrucibleTypes CT.EmptyCtx = CT.EmptyCtx
--   ToCrucibleTypes (tps CT.::> tp) = ToCrucibleTypes tps CT.::> CT.BaseToType tp

type family ToBaseTypesList (ctps :: CT.Ctx CT.CrucibleType) :: [WT.BaseType] where
  ToBaseTypesList CT.EmptyCtx = '[]
  ToBaseTypesList (tps CT.::> tp) = ToBaseType tp ': ToBaseTypesList tps

type family CtxToList (ctx :: CT.Ctx k) :: [k] where
  CtxToList CT.EmptyCtx = '[]
  CtxToList (ctx CT.::> k) = k ': CtxToList ctx

assignmentToList :: Ctx.Assignment f ctx -> PL.List f (CtxToList ctx)
assignmentToList Ctx.Empty = PL.Nil
assignmentToList (args Ctx.:> arg) = arg PL.:< assignmentToList args


-- toFromContextProofStep :: f tps -> g tp -> TL.ToContext (TL.ReverseAcc (CtxToList tps) '[ tp ]) :~: tps Ctx.::> tp
-- toFromContextProofStep _ _ = unsafeCoerce Refl

-- toFromContextProof :: p t -> TL.ToContextFwd (CtxToList t) :~: t
-- toFromContextProof _ = unsafeCoerce Refl

type family ToCrucTypes (wtps :: CT.Ctx WT.BaseType) :: CT.Ctx CT.CrucibleType where
  ToCrucTypes CT.EmptyCtx = CT.EmptyCtx
  ToCrucTypes (wtps CT.::> wtp) = ToCrucTypes wtps CT.::> CT.BaseToType wtp

toCrucTypes :: Ctx.Assignment WT.BaseTypeRepr wtps -> Ctx.Assignment CT.TypeRepr (ToCrucTypes wtps)
toCrucTypes Ctx.Empty = Ctx.Empty
toCrucTypes (wReprs Ctx.:> wRepr) = toCrucTypes wReprs Ctx.:> CT.baseToType wRepr

baseCrucProof :: Ctx.Assignment WT.BaseTypeRepr wtps -> (ToBaseTypes (ToCrucTypes wtps) :~: wtps)
baseCrucProof Ctx.Empty = Refl
baseCrucProof (wtps Ctx.:> _) = case baseCrucProof wtps of
  Refl -> Refl


toFromBaseProof :: CT.TypeRepr tp -> Maybe (tp :~: CT.BaseToType (ToBaseType tp))
toFromBaseProof repr = case CT.asBaseType repr of
  CT.AsBaseType _ -> Just Refl
  _ -> Nothing

fromBaseIndex :: Ctx.Assignment CT.BaseTypeRepr bctx
              -> Ctx.Assignment CT.TypeRepr (ToCrucTypes bctx)
              -> Ctx.Index bctx btp
              -> Ctx.Index (ToCrucTypes bctx) (CT.BaseToType btp)
fromBaseIndex breprs creprs ix =
  case Ctx.intIndex (Ctx.indexVal ix) (Ctx.size creprs) of
    Just (Some ix') | Just Refl <- testEquality (creprs Ctx.! ix') (CT.baseToType $ breprs Ctx.! ix) -> ix'
    _ -> error "Impossible"

toBaseIndex :: Ctx.Assignment CT.BaseTypeRepr bctx
            -> Ctx.Assignment CT.TypeRepr (ToCrucTypes bctx)
            -> Ctx.Index (ToCrucTypes bctx) tp
            -> Ctx.Index bctx (ToBaseType tp)
toBaseIndex breprs creprs ix
  | CT.AsBaseType brepr <- CT.asBaseType (creprs Ctx.! ix)
  , Just (Some ix') <- Ctx.intIndex (Ctx.indexVal ix) (Ctx.size breprs)
  , Just Refl <- testEquality brepr (breprs Ctx.! ix') =
    ix'
toBaseIndex _ _ _ = error "Impossible"

data LabeledValue a b tp = LabeledValue a (b tp)

instance (Eq a, TestEquality b) => TestEquality (LabeledValue a b) where
  LabeledValue a b `testEquality` LabeledValue a' b' =
    case b `testEquality` b' of
      Just Refl -> case a == a' of
        True -> Just Refl
        False -> Nothing
      Nothing -> Nothing

instance (Ord a, OrdF b) => OrdF (LabeledValue a b) where
  compareF (LabeledValue a1 b1) (LabeledValue a2 b2) =
    case compare a1 a2 of
      LT -> LTF
      GT -> GTF
      EQ -> compareF b1 b2

addLabels :: Ctx.Assignment (LabeledValue l a) ctx
          -> Ctx.Assignment f ctx
          -> Ctx.Assignment (LabeledValue l f) ctx
addLabels labels asns = case (labels, asns) of
  (lbls' Ctx.:> LabeledValue lbl _, asns' Ctx.:> asn) -> addLabels lbls' asns' Ctx.:> (LabeledValue lbl asn)
  (Ctx.Empty, Ctx.Empty) -> Ctx.Empty

projectValue :: LabeledValue a b tp -> b tp
projectValue (LabeledValue _ v) = v

projectLabel :: LabeledValue a b tp -> a
projectLabel (LabeledValue l _) = l

instance FC.FunctorFC (LabeledValue a) where
  fmapFC f (LabeledValue a b) = LabeledValue a (f b)

instance FC.FoldableFC (LabeledValue a) where
  foldrFC f s (LabeledValue _ b) = f b s

instance FC.TraversableFC (LabeledValue a) where
  traverseFC f (LabeledValue a b) = LabeledValue a <$> f b

instance (Show a, ShowF b) => ShowF (LabeledValue a b) where
  showF (LabeledValue l v) = concat [ "LabeledValue ", show l, " ", showF v ]

instance (Show a, ShowF b) => Show (LabeledValue a b tp) where
  show (LabeledValue l v) = concat [ "LabeledValue ", show l, " ", showF v ]

type family BaseLitType (tp :: WT.BaseType) :: Type where
  BaseLitType WT.BaseIntegerType = Integer
  BaseLitType WT.BaseBoolType = Bool
  BaseLitType (WT.BaseBVType w) = BV.BV w

data ConstVal tp =
  ConstVal (WT.BaseTypeRepr tp) (BaseLitType tp)

instance Show (ConstVal tp) where
  show (ConstVal WT.BaseIntegerRepr l) = show l
  show (ConstVal WT.BaseBoolRepr l) = show l
  show (ConstVal (WT.BaseBVRepr _) l) = show l
  show _ = "??"

instance ShowF ConstVal

data UserType (tp :: WT.BaseType) where
  UserEnum :: 1 <= n => NR.NatRepr n -> UserType (WT.BaseBVType n)
  UserStruct :: Ctx.Assignment (LabeledValue (T.Text, Maybe (Some UserType)) WT.BaseTypeRepr) tps ->
                UserType (WT.BaseStructType tps)

deriving instance Show (UserType tp)

instance ShowF UserType where

-- | The 'WT.BaseTypeRepr' equivalent representation of a given 'UserType'.
userTypeRepr :: UserType tp -> WT.BaseTypeRepr tp
userTypeRepr ut =
  case ut of
    UserEnum n -> WT.BaseBVRepr n
    UserStruct tps -> WT.BaseStructRepr (FC.fmapFC projectValue tps)

letInStmt :: [T.Text] -> [AS.Stmt] -> AS.Stmt
letInStmt vars stmts = AS.StmtFor "LetIn" (AS.ExprTuple (map AS.ExprLitString vars), AS.ExprTuple []) stmts

unletInStmt :: AS.Stmt -> Maybe ([T.Text], [AS.Stmt])
unletInStmt (AS.StmtFor "LetIn" (exprVars, _) stmts) = Just (getVars exprVars, stmts)
  where
    getVars (AS.ExprTuple vars) = map getVar vars
    getVars _ = error $ "Invalid LetIn"

    getVar (AS.ExprLitString var) = var
    getVar _ = error $ "Invalid LetIn"

unletInStmt _ = Nothing

blockStmt :: [AS.Stmt] -> AS.Stmt
blockStmt stmts = AS.StmtFor "Block" (AS.ExprTuple [], AS.ExprTuple []) stmts

unblockStmt :: AS.Stmt -> Maybe [AS.Stmt]
unblockStmt (AS.StmtFor "Block" _ stmts) = Just stmts
unblockStmt _ = Nothing

trueExpr :: AS.Expr
trueExpr = AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny "TRUE")

falseExpr :: AS.Expr
falseExpr = AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny "FALSE")


-- Extended type data for tracking struct member identifiers. This is necessary since Crucible structs
-- are just tuples, and so extra information is required to resolve ASL struct members to their
-- corresponding Crucible struct index.

type UserStructAcc = Map.Map T.Text StructAccessor

data StructAccessor = forall tps tp. StructAccessor
  { structRepr :: Ctx.Assignment WT.BaseTypeRepr tps
  , structIdx :: Ctx.Index tps tp
  , structFieldExt :: ExtendedTypeData}

deriving instance Show StructAccessor

instance Eq StructAccessor where
  (==) a b = case (a, b) of
    (StructAccessor ar aidx e, StructAccessor br bidx e') |
        Just Refl <- testEquality ar br
      , Just Refl <- testEquality aidx bidx -> e == e'
    _ -> False

type RegisterSig = Map.Map T.Text (Integer, Integer)

data ExtendedTypeData =
    TypeBasic
  | TypeRegister RegisterSig
  | TypeGlobalStruct (Map.Map T.Text T.Text)
  | TypeStruct UserStructAcc
  | TypeTuple [ExtendedTypeData]
  | TypeArray ExtendedTypeData
  deriving (Show, Eq)

data ConstraintHint where
  HintAnyBVSize :: ConstraintHint
  HintMaxBVSize :: 1 WT.<= w => WT.NatRepr w -> ConstraintHint
  HintMaxSignedBVSize :: 1 WT.<= w => WT.NatRepr w -> ConstraintHint

deriving instance Show ConstraintHint


data TypeConstraint where
  ConstraintNone :: TypeConstraint -- wildcard
  ConstraintSingle :: CT.TypeRepr tp -> TypeConstraint -- concrete type
  ConstraintHint :: ConstraintHint -> TypeConstraint -- hints for inferring types
  ConstraintTuple :: [TypeConstraint] -> TypeConstraint

deriving instance Show TypeConstraint

data RegisterKind =
  RegisterR
  deriving (Show, Eq, Ord)

data AccessMode = AccessRead | AccessWrite
  deriving (Show, Eq, Ord)
