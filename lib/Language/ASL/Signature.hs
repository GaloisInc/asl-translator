{-|
Module           : Language.ASL.Signature
Copyright        : (c) Galois, Inc 2019-2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module contains types that describe signatures of ASL functions and
procedures. Procedures have side effects, while functions are side-effect free and
return a single value (which may be a tuple).

Top-level code sequences (like the @instExecute@ field of an instruction) have a trivial type
signature with no inputs (just global refs) and a set of outputs that is the union of all of the
locations touched by that function.

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}


module Language.ASL.Signature (
  -- * Function signatures
    FunctionSignature(..)
  , FunctionArg(..)
  , SomeFunctionSignature(..)
  , SomeInstructionSignature(..)
  , SimpleFunctionSignature(..)
  , SomeSimpleFunctionSignature(..)
  , FuncReturn
  , FuncReturnCtx
  , projectStruct
  , funcSigRepr
  , funcSigBaseRepr
  , funcSigAllArgsRepr
  , someSigName
  , someSigRepr
 -- * Global variable wrapper
  , BaseGlobalVar(..)


  ) where

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Text as T
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import           Language.ASL.Types
import           Language.ASL.StaticExpr
import qualified Language.ASL.Syntax as AS

-- | A 'FunctionSignature' describes the inputs and output of an ASL function.
-- The arguments and return value are tupled to include globals that are read
-- and written respectively.
data FunctionSignature globalReads globalWrites init tps =
  FunctionSignature { funcName :: T.Text
                    -- ^ The name of the function
                    , funcRetRepr :: Ctx.Assignment WT.BaseTypeRepr tps
                    -- ^ The return type of the function
                    , funcArgReprs :: Ctx.Assignment (LabeledValue FunctionArg WT.BaseTypeRepr) init
                    -- ^ The types of the natural arguments of the function
                    , funcGlobalReadReprs :: Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) globalReads
                    -- ^ The globals (transitively) referenced by the function
                    , funcGlobalWriteReprs :: Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) globalWrites
                    -- ^ The globals (transitively) affected by the function
                    , funcStaticVals :: StaticValues
                    , funcIsInstruction :: Bool
                    -- ^ flag indicating that this function is representative of an instruction, and
                    -- therefore requires additional instrumentation to have it serve as a top-level
                    -- transition
                    }
  deriving Show

type FuncReturnCtx globalWrites tps =
  (Ctx.EmptyCtx Ctx.::> (CT.BaseStructType globalWrites) Ctx.::> (CT.BaseStructType tps))

type FuncReturn globalWrites tps =
  CT.SymbolicStructType (FuncReturnCtx globalWrites tps)


data SomeFunctionSignature ret where
  SomeFunctionSignature :: FunctionSignature globalReads globalWrites init tps ->
    SomeFunctionSignature (FuncReturn globalWrites tps)

data SomeInstructionSignature where
  SomeInstructionSignature :: FunctionSignature globalReads globalWrites init Ctx.EmptyCtx ->
    SomeInstructionSignature

projectStruct :: Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) ctx
              -> WT.BaseTypeRepr (CT.BaseStructType ctx)
projectStruct asn = CT.BaseStructRepr (FC.fmapFC projectValue asn)

funcSigRepr :: FunctionSignature globalReads globalWrites init tps
               -> CT.TypeRepr (FuncReturn globalWrites tps)
funcSigRepr fSig = CT.SymbolicStructRepr
  (Ctx.empty Ctx.:> (projectStruct $ funcGlobalWriteReprs fSig) Ctx.:> CT.BaseStructRepr (funcRetRepr fSig))

funcSigBaseRepr :: FunctionSignature globalReads globalWrites init tps
               -> CT.BaseTypeRepr (CT.BaseStructType (FuncReturnCtx globalWrites tps))
funcSigBaseRepr fSig = CT.BaseStructRepr
  (Ctx.empty Ctx.:> (projectStruct $ funcGlobalWriteReprs fSig) Ctx.:> CT.BaseStructRepr (funcRetRepr fSig))

funcSigAllArgsRepr :: FunctionSignature globalReads globalWrites init tps
               -> Ctx.Assignment WT.BaseTypeRepr (init Ctx.::> WT.BaseStructType globalReads)
funcSigAllArgsRepr fSig = FC.fmapFC projectValue (funcArgReprs fSig) Ctx.:> projectStruct (funcGlobalReadReprs fSig)


someSigRepr :: SomeFunctionSignature ret -> CT.TypeRepr ret
someSigRepr (SomeFunctionSignature fSig) = funcSigRepr fSig

someSigName :: SomeFunctionSignature ret -> T.Text
someSigName (SomeFunctionSignature fSig) = funcName fSig

deriving instance Show (SomeFunctionSignature ret)

instance ShowF SomeFunctionSignature

-- | A named function argument with an associated 'AS.Type'
data FunctionArg = FunctionArg
  { argName :: T.Text
  , argType :: AS.Type
  }
  deriving Show

-- | A 'SimpleFunctionSignature' describes the inputs and output of an ASL function.
-- This is an intermediate representation of 'FunctionSignature' before it has
-- been fully monomorphized.
data SimpleFunctionSignature globalReads globalWrites  =
  SimpleFunctionSignature { sfuncName :: T.Text
                           -- ^ The name of the function
                           , sfuncRet :: [AS.Type]
                           -- ^ The return type of the function
                           , sfuncArgs :: [FunctionArg]
                           -- ^ The types of the natural arguments of the function
                           , sfuncGlobalReadReprs :: Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) globalReads
                           -- ^ The globals (transitively) referenced by the function
                           , sfuncGlobalWriteReprs :: Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) globalWrites
                           -- ^ The globals (transitively) affected by the function
                           }
  deriving (Show)

data SomeSimpleFunctionSignature where
  SomeSimpleFunctionSignature ::
    SimpleFunctionSignature globalReads globalWrites -> SomeSimpleFunctionSignature

-- | A wrapped 'CCG.GlobalVar' which is a 'WT.BaseType'
newtype BaseGlobalVar tp = BaseGlobalVar { unBaseVar :: CCG.GlobalVar (CT.BaseToType tp) }
  deriving (Show)

instance ShowF BaseGlobalVar
