{-|
Module           : Language.ASL.Globals.Definitions
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module provides the base set of definitions for deriving
the globals in "Language.ASL.Globals". Each 'Global' represents
a global variable from the ASL specification, and is either
"tracked" or "untracked".

The tracked globals (specified in "trackedGlobals'") are variables
that are given as input and taken as output to each instruction.
They represent the state transition taken by each instruction.

The untracked globals (specified in "untrackedGlobals'") are variables
that may be read by the ASL specification for each instruction, but
with an undefined value. Any writes to these globals are preserved
for the duration of a single instruction (i.e. across multiple
function calls) but their final value is discarded.
They represent under-specified pieces of the processor state, whose
specific values should not be relevant during normal execution.

Either 'Global' kind may provide a 'GlobalDomain' which represents a
restriction on valid values for that global. The translator will add
assertions that these domains are respected at the beginning and end
of each instruction.

-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.ASL.Globals.Definitions
  ( simpleGlobals'
  , trackedGlobals'
  , MemoryBaseType
  , memoryGlobal
  , untrackedGlobals'
  , flatTrackedGlobals'
  , gprGlobals'
  , simdGlobals'
  , forSome
  , MaxGPR
  , AllGPRBaseType
  , MaxSIMD
  , AllSIMDBaseType
  , maxGPRRepr
  , maxSIMDRepr
  , UnitType
  ) where

import           GHC.TypeNats ( KnownNat )
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Context ( Assignment, empty, pattern (:>), (<++>) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR

import qualified Data.Text as T
import           Data.Parameterized.NatRepr ( type (<=) )
import           Data.Parameterized.Classes
import qualified What4.Interface as WI
import qualified What4.Concrete as WI

import           Language.ASL.Globals.Types
import           Language.ASL.StaticExpr ( bitsToInteger )

-- | The maximum index for a user register
type MaxGPR = 14
-- | The maximum index for a vector register
type MaxSIMD = 31

-- type ArrayBaseType idxsz valsz = WI.BaseArrayType(EmptyCtx ::> WI.BaseBVType idxsz) (WI.BaseBVType valsz)

-- type MemoryBaseType = ArrayBaseType 32 8
-- type AllGPRBaseType = ArrayBaseType 4 32
-- type AllSIMDBaseType = ArrayBaseType 8 128
type MemoryBaseType = WI.BaseBVType 146
type AllGPRBaseType = WI.BaseBVType 148
type AllSIMDBaseType = WI.BaseBVType 149
type UnitType = WI.BaseStructType Ctx.EmptyCtx

-- | A 'NR.NatRepr' for 'MaxGPR'
maxGPRRepr :: NR.NatRepr MaxGPR
maxGPRRepr = NR.knownNat

-- | A 'NR.NatRepr' for 'MaxSIMD'
maxSIMDRepr :: NR.NatRepr MaxSIMD
maxSIMDRepr = NR.knownNat


-- | Reversed arguments for 'viewSome'
forSome :: Some f -> (forall tp . f tp -> r) -> r
forSome (Some x) f = f x

-- | All simple (non-register and non-memory) "tracked" global ASL variables.
simpleGlobals' :: Some (Assignment Global)
simpleGlobals' =
  Some $ Ctx.empty
  -- meta-state indicating abnormal execution status
  :> bool "__AssertionFailure"
  :> bool "__UndefinedBehavior"
  :> bool "__UnpredictableBehavior"
  :> def "__DummyValue" (knownRepr :: WI.BaseTypeRepr UnitType) domainUnbounded
  -- meta-state reifying information about this encoding
  :> bv @32 "__ThisInstr"
  -- tracking additional execution flags
  :> bool "__PendingInterrupt"
  :> bool "__PendingPhysicalSError"
  :> bool "__Sleeping"
  :> bool "__BranchTaken"
  :> bool "__EndOfInstruction"
  :> bool "__conditionPassed"
  :> bv @32 "_PC"
  -- rest of the processor state is unconstrained
  :> bv @32 "FPSCR"
  :> bv @1 "PSTATE_A"
  :> bv @2 "PSTATE_BTYPE"
  :> bv @1 "PSTATE_C"
  :> bv @1 "PSTATE_DIT"
  :> bv @1 "PSTATE_E"
  :> bv @2 "PSTATE_EL"
  :> bv @1 "PSTATE_F"
  :> bv @4 "PSTATE_GE"
  :> bv @1 "PSTATE_I"
  :> bv @1 "PSTATE_IL"
  :> bv @8 "PSTATE_IT"
  :> bv @1 "PSTATE_N"
  :> bv @1 "PSTATE_PAN"
  :> bv @1 "PSTATE_Q"
  :> bv @1 "PSTATE_SP"
  :> bv @1 "PSTATE_SS"
  :> bv @1 "PSTATE_SSBS"
  :> bv @1 "PSTATE_T"
  :> bv @1 "PSTATE_TCO"
  :> bv @1 "PSTATE_UAO"
  :> bv @1 "PSTATE_V"
  :> bv @1 "PSTATE_Z"
  :> bv @1 "PSTATE_nRW"

-- | All 'Global's as they are configured in the ASL global state, with GPRs and SIMDs as nested globals.
trackedGlobals' :: Some (Assignment Global)
trackedGlobals' =
  forSome simpleGlobals' $ \simpleGlobals'' ->
  Some $ simpleGlobals''
  -- the registers
  :> gprGlobal
  :> simdGlobal
  :> memoryGlobal

-- | A representation of all global variables with a unique 'Global' for each GPR and SIMD
flatTrackedGlobals' :: Some (Assignment Global)
flatTrackedGlobals' =
  forSome simpleGlobals' $ \simpleGlobals'' ->
  forSome gprGlobals' $ \gprGlobals'' ->
  forSome simdGlobals' $ \simdGlobals'' ->
  Some $
  (simpleGlobals''
  <++> gprGlobals''
  <++> simdGlobals'') :> memoryGlobal

-- | The 'Global' representing all of memory.
memoryGlobal :: Global MemoryBaseType
memoryGlobal = def "__Memory" knownRepr domainUnbounded

-- | The 'Global' reflecting the entire state of the user registers (defined in ASL as "GPRS")
gprGlobal :: Global AllGPRBaseType
gprGlobal = def "GPRS" knownRepr domainUnbounded

-- | The user registers expanded into a distinct 'Global' for each register.
gprGlobals' :: Some (Assignment Global)
gprGlobals' = Ctx.fromList $
  map (\i -> Some $ def ("_R" <> (T.pack $ show i))
        (knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 32)) domainUnbounded) [0 .. (NR.intValue maxGPRRepr)]

-- | The 'Global' reflecting the entire state of the vector registers (defined in ASL as "SIMDS")
simdGlobal :: Global AllSIMDBaseType
simdGlobal = def "SIMDS" knownRepr domainUnbounded

-- | The vector registers expanded into a distinct 'Global' for each register.
simdGlobals' :: Some (Assignment Global)
simdGlobals' = Ctx.fromList $
  map (\i -> Some $ def ("_V" <> (T.pack $ show i))
        (knownRepr :: WI.BaseTypeRepr (WI.BaseBVType 128)) domainUnbounded) [0 .. (NR.intValue maxSIMDRepr)]

def :: T.Text -> WI.BaseTypeRepr tp -> GlobalDomain tp -> Global tp
def nm repr dom = Global nm repr dom

bool :: T.Text -> Global WI.BaseBoolType
bool nm = def nm WI.BaseBoolRepr domainUnbounded

bv :: forall n. 1 <= n => KnownNat n => T.Text -> Global (WI.BaseBVType n)
bv nm = def nm (WI.BaseBVRepr WI.knownNat) domainUnbounded

bvsingle :: forall n. 1 <= n => KnownNat n => T.Text -> BV.BV n -> Global (WI.BaseBVType n)
bvsingle nm v = def nm WI.knownRepr (domainSingleton (WI.ConcreteBV WI.knownNat v))

bvbits :: forall n. 1 <= n => KnownNat n => String -> T.Text -> Global (WI.BaseBVType n)
bvbits bits nm  =
  if fromIntegral (length bits) == (WI.intValue $ WI.knownNat @n) then
    def nm WI.knownRepr
      (domainSingleton (WI.ConcreteBV WI.knownNat (BV.mkBV WI.knownNat $ bitsToInteger $ parseBits bits)))
  else error $ "Bad bits: " ++ show bits

noflag :: T.Text -> Global WI.BaseBoolType
noflag nm = def nm WI.BaseBoolRepr (domainSingleton (WI.ConcreteBool False))

parseBits :: String -> [Bool]
parseBits bits = case bits of
  ('0' : rest) -> False : parseBits rest
  ('1' : rest) -> True : parseBits rest
  [] -> []
  s -> error $ "bad bitstring: " ++ show s

-- | 'Global's which are not explicitly tracked by the translation. These
-- will have an undefined (but possibly restricted) initial value at the
-- beginning of each instruction, and any writes will be discarded at the end.
untrackedGlobals' :: Some (Assignment Global)
untrackedGlobals' = Some $ empty
  -- the debug flag should not be set
  :> bvsingle @1 "PSTATE_D" (BV.zero WI.knownNat)
   -- processor mode should always be M32_User
  :> bvbits @5 "10000" "PSTATE_M"
  -- memory model
  :> noflag "__ExclusiveLocal"
  -- this is set by the instruction preamble when it is in a conditional block.
  -- it is used to determine if the IT register should be incremented, which is ultimately used
  -- to determine where the end of a conditional block is
  :> bool "ShouldAdvanceIT"
  -- this is initialized before it is read, so we don't need to track it
  -- the translator assigns this to a copy of SIMDS as its initial value
  :> def "SIMDS_clone" (knownRepr :: WI.BaseTypeRepr AllSIMDBaseType) domainUnbounded
  :> bv @4 "__currentCond"
  :> bv @3 "__ThisInstrEnc"
  -- system registers
  :> bv @32 "CPACR"
  :> bv @32 "CPACR_EL1"
  :> bv @32 "CPTR_EL2"
  :> bv @32 "CPTR_EL3"
  :> bv @32 "DACR"
  :> bv @32 "DBGDSCRext"
  :> bv @1 "DBGEN"
  :> bv @32 "DBGOSDLR"
  :> bv @32 "DBGOSLSR"
  :> bv @32 "DBGPRCR"
  :> bv @32 "DBGPRCR_EL1"
  :> bv @32 "DFAR"
  :> bv @32 "DFSR"
  :> bv @32 "DISR"
  :> bv @64 "DISR_EL1"
  :> bv @32 "DLR"
  :> bv @64 "DLR_EL0"
  :> bv @32 "DSPSR"
  :> bv @32 "DSPSR_EL0"
  :> bv @32 "DTRRX"
  :> bv @32 "DTRTX"
  :> bv @32 "EDSCR"
  :> bv @32 "ELR_hyp"
  :> bv @1 "EventRegister"
  :> bv @32 "FPEXC"
  :> bv @32 "FPSID"
  :> bv @32 "FPSR"
  :> bv @32 "HCPTR"
  :> bv @32 "HCR"
  :> bv @32 "HCR2"
  :> bv @64 "HCR_EL2"
  :> bv @32 "HDCR"
  :> bv @32 "HDFAR"
  :> bv @32 "HIFAR"
  :> bv @32 "HPFAR"
  :> bv @32 "HSCTLR"
  :> bv @32 "HSR"
  :> bv @32 "HVBAR"
  :> bv @32 "IFAR"
  :> bv @32 "IFSR"
  :> bv @32 "LR_mon"
  :> bv @32 "MDCR_EL2"
  :> bv @32 "MDCR_EL3"
  :> bv @32 "MDSCR_EL1"
  :> bv @32 "MVBAR"
  :> bv @32 "MVFR0"
  :> bv @32 "MVFR1"
  :> bv @32 "MVFR2"
  :> bv @32 "NSACR"
  :> bv @32 "OSDLR_EL1"
  :> bv @32 "OSLSR_EL1"
  :> bv @32 "SCR"
  :> bv @32 "SCR_EL3"
  :> bv @32 "SCTLR"
  :> bv @64 "SCTLR_EL1"
  :> bv @64 "SCTLR_EL2"
  :> bv @64 "SCTLR_EL3"
  :> bv @32 "SDCR"
  :> bv @32 "SDER"
  :> bv @1 "SPIDEN"
  :> bv @32 "SPSR_EL1"
  :> bv @32 "SPSR_EL2"
  :> bv @32 "SPSR_EL3"
  :> bv @32 "SPSR_abt"
  :> bv @32 "SPSR_fiq"
  :> bv @32 "SPSR_hyp"
  :> bv @32 "SPSR_irq"
  :> bv @32 "SPSR_mon"
  :> bv @32 "SPSR_svc"
  :> bv @32 "SPSR_und"
  :> bv @32 "SP_mon"
  :> bv @32 "TTBCR"
  :> bv @32 "TTBCR_S"
  :> bv @32 "VBAR"
  :> bv @32 "VDFSR"
  :> bv @32 "VDISR"
  :> bv @64 "VDISR_EL2"
  :> bv @64 "VSESR_EL2"

-- These all manifest when MemSingle isn't stubbed
  -- :> intarraybv @32 "DBGBCR"
  -- :> intarraybv @64 "DBGBCR_EL1"
  -- :> bv @32 "DBGDIDR"
  -- :> bv @32 "DBGVCR"
  -- :> bv @64 "ID_AA64DFR0_EL1"
  -- :> bool "InGuardedPage"
  -- :> bv @64 "MPAM0_EL1"
  -- :> bv @64 "MPAM1_EL1"
  -- :> bv @64 "MPAM2_EL2"
  -- :> bv @64 "MPAM3_EL3"
  -- :> bv @64 "MPAMHCR_EL2"
  -- :> bv @64 "MPAMIDR_EL1"
  -- :> bv @64 "MPAMVPM0_EL2"
  -- :> bv @64 "MPAMVPM1_EL2"
  -- :> bv @64 "MPAMVPM2_EL2"
  -- :> bv @64 "MPAMVPM3_EL2"
  -- :> bv @64 "MPAMVPM4_EL2"
  -- :> bv @64 "MPAMVPM5_EL2"
  -- :> bv @64 "MPAMVPM6_EL2"
  -- :> bv @64 "MPAMVPM7_EL2"
  -- :> bv @64 "MPAMVPMV_EL2"
  -- :> bv @64 "TCR_EL1"
  -- :> bv @64 "TCR_EL2"
  -- :> bv @32 "TCR_EL3"
  -- :> bv @64 "TFSRE0_EL1"
  -- :> bv @64 "TFSR_EL1"
  -- :> bv @64 "TFSR_EL2"
  -- :> bv @64 "TFSR_EL3"
