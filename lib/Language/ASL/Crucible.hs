{-|
Module           : Language.ASL.Crucible
Copyright        : (c) Galois, Inc 2019-2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module is the entry point for deriving Crucible CFGs from
ASL functions and instructions. The translation from ASL
syntax into Crucible is handled by "Language.ASL.Translation",
while this module provides the framework for specifying
the expected signature for the derived function.

The core functionality is provided by 'functionToCrucible'
and 'instructionToCrucible'. Fundamentally instructions
and functions are the same (a list of ASL statements, with
a corresponding list of arguments and a return type), however
all instructions share the same set of global reads/writes
(defined as 'G.StructGlobalsCtx').

-}

{-# OPTIONS_HADDOCK not-home #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

module Language.ASL.Crucible (
  -- * Deriving a Crucible CFG from ASL
    functionToCrucible
  , instructionToCrucible
  -- * Wrappers for translated functions/instructions
  , GenFunction(..)
  , Function
  , Instruction


  , funcRetRepr
  , funcArgReprs
  , funcSigBaseRepr
  , funcSigAllArgsRepr
  , funcGlobalReadReprs
  , funcGlobalWriteReprs

  -- re-exports

  -- syntax extension
  , ASLExt
  , ASLApp(..)
  , ASLStmt
  , aslExtImpl
  -- function signatures
  , FunctionSignature
  , SomeFunctionSignature(..)
  , LabeledValue(..)
  -- preprocessing
  , UserType
  , Definitions(..)
  -- translation
  , BaseGlobalVar(..)
  , Overrides(..)
  ) where

import qualified Control.Exception as X
import           Control.Monad.ST ( stToIO, ST )
import qualified Data.Map as Map
import qualified Data.STRef as STRef
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Nonce ( newSTNonceGenerator )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.Map as MapF
import qualified Data.Text as T
import qualified Data.Set as Set

import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.CFG.SSAConversion as CCS
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import qualified What4.Utils.StringLiteral as WT
import qualified What4.FunctionName as WFN
import qualified What4.ProgramLoc as WP

import qualified Language.ASL.Syntax as AS

import           Language.ASL.Translation.Exceptions ( TranslationException(..) )
import           Language.ASL.Crucible.Extension ( ASLExt, ASLApp(..), ASLStmt(..), aslExtImpl )
import           Language.ASL.Signature
import           Language.ASL.Translation.Preprocess ( Definitions(..) )
import           Language.ASL.Translation ( TranslationState(..), Overrides(..)
                                          , InnerGenerator
                                          , translateBody, overrides, unliftGenerator)
import           Language.ASL.Types ( UserType(..)
                                    , ToCrucTypes
                                    , toCrucTypes
                                    , LabeledValue(..)
                                    , projectValue
                                    , toBaseIndex)
import           Language.ASL.StaticExpr
import qualified Language.ASL.Globals as G

import qualified Lang.Crucible.CFG.Extension as CCExt

-- FIXME: this should be moved somewhere general
import           What4.Utils.Log ( HasLogCfg, getLogCfg )


data GenFunction arch innerReads innerWrites outerReads outerWrites init tps =
   GenFunction { funcSig :: FunctionSignature innerReads innerWrites init tps
               , funcCFG :: CCC.SomeCFG (ASLExt arch) (ToCrucTypes init) (FuncReturn innerWrites tps)
               , funcGlobalReads :: Ctx.Assignment BaseGlobalVar innerReads
               , funcOuterReadReprs :: Ctx.Assignment (LabeledValue T.Text CT.BaseTypeRepr) outerReads
               , funcOuterWriteReprs :: Ctx.Assignment (LabeledValue T.Text CT.BaseTypeRepr) outerWrites
               , funcDepends :: Set.Set (T.Text, StaticValues)
               , funcReadProj :: forall tp. Ctx.Index outerReads tp -> Maybe (Ctx.Index innerReads tp)
               , funcWriteProj :: forall tp. Ctx.Index outerWrites tp -> Maybe (Ctx.Index innerWrites tp)
               }
type Function arch globalReads globalWrites init tps =
  GenFunction arch globalReads globalWrites globalReads globalWrites init tps

type Instruction arch globalReads globalWrites init =
  GenFunction arch globalReads globalWrites G.StructGlobalsCtx G.StructGlobalsCtx init Ctx.EmptyCtx

-- | This type alias is a constraint relating the 'globals' (base types) to the
-- actual return type in terms of Crucible types
--
-- The constraint is simple but a bit annoying to write
type ReturnsGlobals ret globalWrites tps = (ret ~ FuncReturn globalWrites tps)

-- | Translate an ASL function (signature plus statements) into a Crucible function
--
-- We bundle up the signature, CFG, and allocated globals.  We need to keep the
-- globals around for re-use during simulation.
--
-- The overall strategy is to allocate a Crucible global variable for each part
-- of the CPU state (i.e., machine register) that could be read or written by
-- the procedure.  We'll use symbolic simulation to determine the effect of the
-- procedure on each register.
--
-- Every function takes its natural argument list plus one extra argument: the
-- register file (a struct of all of the register values).  When the procedure
-- starts, we'll copy all of the values from the register struct into the globals.
--
-- NOTE: The signature computation MUST account for the UNPREDICTABLE and
-- UNDEFINED globals.  They may be accessed during the translation and must be
-- available in the 'TranslationState'
functionToCrucible' :: forall arch innerReads innerWrites outerReads outerWrites init tps ret
                     . HasLogCfg
                    => ReturnsGlobals ret innerWrites tps
                    => Ctx.Assignment (LabeledValue T.Text CT.BaseTypeRepr) outerReads
                    -> Ctx.Assignment (LabeledValue T.Text CT.BaseTypeRepr) outerWrites
                    -> (forall tp. Ctx.Index outerReads tp -> Maybe (Ctx.Index innerReads tp))
                    -> (forall tp. Ctx.Index outerWrites tp -> Maybe (Ctx.Index innerWrites tp))
                    -> Definitions arch
                    -> FunctionSignature innerReads innerWrites init tps
                    -> CFH.HandleAllocator
                    -> [AS.Stmt]
                    -> IO (GenFunction arch innerReads innerWrites outerReads outerWrites init tps)
functionToCrucible' readReprs writeReprs projReads projWrites defs sig hdlAlloc stmts = do
  let argReprs = toCrucTypes $ FC.fmapFC (projectValue) (funcArgReprs sig)
  let retRepr = funcSigRepr sig
  hdl <- CFH.mkHandle' hdlAlloc (WFN.functionNameFromText (funcName sig)) argReprs retRepr
  globalReadVars <- FC.traverseFC allocateGlobal (funcGlobalReadReprs sig)
  let pos = WP.InternalPos
  (CCG.SomeCFG cfg0, depends) <- stToIO $ defineCCGFunction pos hdl $ \refs ->
    funcDef defs sig refs globalReadVars stmts
  return $
       GenFunction { funcSig = sig
                   , funcCFG = CCS.toSSA cfg0
                   , funcGlobalReads = globalReadVars
                   , funcOuterReadReprs = readReprs
                   , funcOuterWriteReprs = writeReprs
                   , funcDepends = depends
                   , funcReadProj = projReads
                   , funcWriteProj = projWrites
                   }
  where
    allocateGlobal :: forall tp . LabeledValue T.Text WT.BaseTypeRepr tp -> IO (BaseGlobalVar tp)
    allocateGlobal (LabeledValue name rep) =
      BaseGlobalVar <$> CCG.freshGlobalVar hdlAlloc name (CT.baseToType rep)

functionToCrucible :: forall arch globalReads globalWrites init tps ret
                    . HasLogCfg
                   => ReturnsGlobals ret globalWrites tps
                   => Definitions arch
                   -> FunctionSignature globalReads globalWrites init tps
                   -> CFH.HandleAllocator
                   -> [AS.Stmt]
                   -> IO (Function arch globalReads globalWrites init tps)
functionToCrucible defs sig = do
  functionToCrucible' (funcGlobalReadReprs sig) (funcGlobalWriteReprs sig) Just Just defs sig

instructionToCrucible :: forall arch globalReads globalWrites init ret
                       . HasLogCfg
                      => ReturnsGlobals ret G.StructGlobalsCtx Ctx.EmptyCtx
                      => Definitions arch
                      -> FunctionSignature globalReads globalWrites init Ctx.EmptyCtx
                      -> CFH.HandleAllocator
                      -> [AS.Stmt]
                      -> IO (Instruction arch globalReads globalWrites init)
instructionToCrucible defs sig hdlAlloc stmts = do
  projReads <- case G.getGlobalsSubMap (funcGlobalReadReprs sig) of
    Left err -> X.throw $ GlobalsError ("instructionToCrucible: " ++ err)
    Right r -> return r

  projWrites <- case G.getGlobalsSubMap (funcGlobalWriteReprs sig) of
    Left err -> X.throw $ GlobalsError ("instructionToCrucible: " ++ err)
    Right r -> return $ r

  let
    projR :: forall tp. Ctx.Index G.StructGlobalsCtx tp -> Maybe (Ctx.Index globalReads tp)
    projR idx = MapF.lookup idx projReads

    projW :: forall tp. Ctx.Index G.StructGlobalsCtx tp -> Maybe (Ctx.Index globalWrites tp)
    projW idx = MapF.lookup idx projWrites

  functionToCrucible' G.trackedGlobalReprs G.trackedGlobalReprs projR projW defs sig hdlAlloc stmts


defineCCGFunction :: CCExt.IsSyntaxExtension ext
               => WP.Position
               -> CFH.FnHandle init ret
               -> ((STRef.STRef h (Set.Set (T.Text,StaticValues))) ->
                    CCG.FunctionDef ext t init ret (ST h))
               -> ST h ((CCG.SomeCFG ext init ret, Set.Set (T.Text,StaticValues)))
defineCCGFunction p h f = do
    ng <- newSTNonceGenerator
    funDepRef <- STRef.newSTRef Set.empty
    (cfg, _) <- CCG.defineFunction p ng h (f funDepRef)
    funDeps <- STRef.readSTRef funDepRef
    return (cfg, funDeps)

funcDef :: HasLogCfg
        => ReturnsGlobals ret innerWrites tps
        => Definitions arch
        -> FunctionSignature innerReads innerWrites init tps
        -> STRef.STRef h (Set.Set (T.Text, StaticValues))
        -> Ctx.Assignment BaseGlobalVar outerReads
        -> [AS.Stmt]
        -> Ctx.Assignment (CCG.Atom s) (ToCrucTypes init)
        -> (TranslationState arch h ret s, InnerGenerator h s arch ret (CCG.Expr (ASLExt arch) s ret))
funcDef defs sig hdls globalReads stmts args =
  (funcInitialState defs sig hdls globalReads args, defineFunction sig stmts args)

funcInitialState :: forall init innerReads innerWrites outerReads tps h s arch ret
                  . HasLogCfg
                 => ReturnsGlobals ret innerWrites tps
                 => Definitions arch
                 -> FunctionSignature innerReads innerWrites init tps
                 -> STRef.STRef h (Set.Set (T.Text, StaticValues))
                 -> Ctx.Assignment BaseGlobalVar outerReads
                 -> Ctx.Assignment (CCG.Atom s) (ToCrucTypes init)
                 -> TranslationState arch h ret s
funcInitialState defs sig funDepRef globalReads args =
  TranslationState { tsArgAtoms = Ctx.forIndex (Ctx.size args) addArgument Map.empty
                   , tsVarRefs = Map.empty
                   , tsExtendedTypes = defExtendedTypes defs
                   , tsGlobals = FC.foldrFC addGlobal Map.empty globalReads
                   , tsConsts = defConsts defs
                   , tsEnums = defEnums defs
                   , tsFunctionSigs = fst <$> defSignatures defs
                   , tsUserTypes = defTypes defs
                   , tsHandle = funDepRef
                   , tsStaticValues = Map.union (funcStaticVals sig) G.staticGlobals
                   , tsSig = SomeFunctionSignature sig
                   , tsLogCfg = getLogCfg
                   , tsOverrides = overrides
                   }
  where
    addArgument :: forall tp
                 . Map.Map T.Text (Some (CCG.Atom s))
                -> Ctx.Index (ToCrucTypes init) tp
                -> Map.Map T.Text (Some (CCG.Atom s))
    addArgument m idx =
      let
        argReprs = FC.fmapFC projectValue (funcArgReprs sig)
        inArgReprs = FC.fmapFC (CCG.typeOfAtom) args
        bidx = toBaseIndex argReprs inArgReprs idx
      in
        Map.insert (projectFunctionName (funcArgReprs sig Ctx.! bidx)) (Some (args Ctx.! idx)) m
    addGlobal (BaseGlobalVar gv) m =
      Map.insert (CCG.globalName gv) (Some gv) m

projectFunctionName :: LabeledValue FunctionArg a tp -> T.Text
projectFunctionName (LabeledValue (FunctionArg nm _) _) = nm

defineFunction :: HasLogCfg
               => ReturnsGlobals ret globalWrites tps
               => FunctionSignature globalReads globalWrites init tps
               -> [AS.Stmt]
               -> Ctx.Assignment (CCG.Atom s) (ToCrucTypes init)
               -> InnerGenerator h s arch ret (CCG.Expr (ASLExt arch) s ret)
defineFunction sig stmts _args = do
  unliftGenerator $ translateBody stmts
  let errmsg = "Function " <> funcName sig <> " does not return."
  errStr <- CCG.mkAtom (CCG.App (CCE.StringLit $ WT.UnicodeLiteral errmsg))
  CCG.reportError (CCG.AtomExpr errStr)

{- Note [Call Translation]

Functions may return both values or update processor state through side effects.
Our challenge in this code is to turn these imperative procedures into pure
functions.  The strategy will be to arrange it so that, in addition to its
natural set of parameters, each function takes an entire machine state as a
BaseStruct.  It will also return an entire BaseStruct register state.

At function initialization time, the function will copy all of its input
machine state into a set of locals (Crucible or globals).  Before calling a
function, the caller takes a snapshot of the current machine state (from the
refs) to construct the BaseStruct to pass to the callee.  After a function call
returns, the caller will assign the contents of the register state back to its
locals (refs).

Question: do we need any additional components to the return value of
procedures?  Anything that isn't a global is local, and local modifications
can't be reflected to callers.

Note that we have an additional unusual constraint: we need to represent calls
in any context as uninterpreted functions, since we don't want to eagerly expand
definitions of functions.  Doing so produces an enormous code explosion that we
can't handle.  Crucible can support uninterpreted functions via what4; however,
they aren't exactly first class.  Uninterpreted functions can only take as
arguments and return base types.  Crucible doesn't have great support for
working with base types.

Beyond the normal machine registers, we introduce two extra state variables:
- Undefined
- Unpredictable

Each is a boolean that starts as False and is switched to True if an instruction
has undefined or unpredictable behavior, respectively.

-}
