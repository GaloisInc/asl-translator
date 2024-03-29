{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
module Language.ASL.Translation.Exceptions (
      TranslationException(..)
  ) where

import qualified Control.Exception as X
import qualified Data.Text as T
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT

import qualified Language.ASL.Syntax as AS


import           Language.ASL.Signature
import           Language.ASL.Types
import           Language.ASL.StaticExpr

data TranslationException = forall ret . NoReturnInFunction (SomeFunctionSignature ret)
                          | forall tp . InvalidReturnType (CT.TypeRepr tp)
                          | forall tp1 tp2 .  UnexpectedExprType (Maybe AS.Expr) (CT.TypeRepr tp1) (CT.TypeRepr tp2)
                          -- ^ Expression, actual type, expected type
                          | UnsupportedType AS.Type
                          | UnsupportedExpr AS.Expr
                          | UnsupportedStmt AS.Stmt
                          | UnsupportedLVal AS.LValExpr
                          | InvalidZeroLengthBitvector
                          | forall tp1 tp2 . UnexpectedBitvectorLength (CT.TypeRepr tp1) (CT.TypeRepr tp2)
                          | forall w1 w2. ExpectedBVSizeLeq (WT.NatRepr w1) (WT.NatRepr w2)
                          | forall tp . ExpectedBVType AS.Expr (CT.TypeRepr tp)
                          | forall tp . ExpectedBVType' (Maybe AS.Expr) (CT.TypeRepr tp)
                          | forall tp . ExpectedBVLValType AS.LValExpr (CT.TypeRepr tp)
                          | forall tp . ExpectedIntegerType AS.Expr (CT.TypeRepr tp)
                          | forall tp . ExpectedStructType (Maybe AS.Expr) (CT.TypeRepr tp)
                          | forall tp . UnsupportedComparisonType (Maybe AS.Expr) (CT.TypeRepr tp)
                          | UnboundName T.Text
                          | LocalAlreadyDefined T.Text
                          | UnsupportedBinaryOperator AS.BinOp
                          | EmptySetElementList AS.Expr
                          | MalformedConditionalExpression AS.Expr
                          | forall tp . ExpectedBaseTypeRepr (CT.TypeRepr tp)
                          | forall tp . ExpectedBaseType AS.Expr (CT.TypeRepr tp)
                          | forall tp . ExpectedBaseTypeArgument T.Text (CT.TypeRepr tp)
                          | MissingFunctionDefinition T.Text
                          | ExpectedFunctionSignature T.Text
                          | ExpectedProcedureSignature T.Text
                          | forall tps . InvalidArgumentTypes T.Text (Ctx.Assignment CT.TypeRepr tps)
                          | forall tp1 tp2 . UnexpectedProcedureReturn (CT.TypeRepr tp1) (CT.TypeRepr tp2)
                          | MissingGlobal T.Text
                          | forall t. Show t => MissingGlobalStructField t T.Text
                          | forall tp . UnexpectedGlobalType T.Text (CT.TypeRepr tp)
                          | UnexpectedType AS.QualifiedIdentifier
                          | InvalidSliceRange Integer Integer
                          | forall tp . InvalidSlice Integer Integer (CT.TypeRepr tp)
                          | forall w w'. InvalidSymbolicSlice (WT.NatRepr w) (WT.NatRepr w')
                          | TypeUnificationFailure AS.Type TypeConstraint StaticValues
                          | TypesUnificationFailure [AS.Type] TypeConstraint
                          | RequiresTypeConstraint AS.Expr TypeConstraint
                          | ReturnTypeUnificationFailure AS.Type AS.Type StaticValues
                          | StructFieldMismatch AS.Expr
                          | RequiredConcreteValue AS.Expr StaticValues
                          | forall tp. InvalidLValSlice AS.Slice TypeConstraint (CT.TypeRepr tp)
                          | UnsupportedSlice AS.Slice TypeConstraint
                          | CannotMonomorphizeFunctionCall T.Text StaticValues
                          | CannotMonomorphizeOverloadedFunctionCall T.Text [AS.Expr]
                          | CannotStaticallyEvaluateType AS.Type StaticValues
                          | CannotDetermineBVLength (Maybe AS.Expr) TypeConstraint
                          | UnexpectedExtendedType AS.Expr ExtendedTypeData
                          | ConflictingExtendedTypeData T.Text ExtendedTypeData ExtendedTypeData
                          | MissingRegisterField AS.Expr T.Text
                          | MissingStructField AS.Expr T.Text
                          | InvalidOverloadedFunctionCall T.Text [AS.Expr]
                          | BadMemoryAccess AS.Expr
                          | StaticEvaluationOfFalseAssertion AS.Expr
                          | UnexpectedInlineFunction T.Text
                          | UnexpectedNothing
                          | TranslationError String
                          | UNIMPLEMENTED String
                          | forall tp. InvalidStructUpdate AS.LValExpr (CT.TypeRepr tp)
                          | UnexpectedReturnInStmtCall
                          | UnexpectedReturnInExprCall
                          | BindingFailure String
                          | BadASLFunctionCall
                          | GlobalsError String
                          | TExceptions [TranslationException]


deriving instance Show TranslationException

instance X.Exception TranslationException
