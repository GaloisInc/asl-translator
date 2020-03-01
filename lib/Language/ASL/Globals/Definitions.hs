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
  , MaxSIMD
  , maxGPRRepr
  , maxSIMDRepr
  ) where

import           GHC.Natural ( naturalFromInteger )

import           Control.Applicative ( Const(..) )
import           Control.Monad ( forM, foldM )
import           Control.Monad.Except ( throwError )
import qualified Control.Monad.Except as ME

import           GHC.TypeNats ( KnownNat )
import           Data.Parameterized.Some ( Some(..), viewSome )
import           Data.Parameterized.Ctx ( type (<+>) )
import           Data.Parameterized.Context ( EmptyCtx, (::>), Assignment, empty, pattern (:>), (<++>) )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableFC as FC

import           Data.Maybe ( catMaybes )
import           Data.List ( intercalate )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Text as T
import           Data.Parameterized.NatRepr ( type (<=) )
import           Data.Parameterized.Classes
import qualified What4.Interface as WI
import qualified What4.Concrete as WI

import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT

import           Language.ASL.Signature
import           Language.ASL.Types
import           Language.ASL.Globals.Types
import           Language.ASL.StaticExpr ( bitsToInteger )

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

type MaxGPR = 14
type MaxSIMD = 31

type MemoryBaseType = WI.BaseArrayType (EmptyCtx ::> WI.BaseBVType 32) (WI.BaseBVType 8)

maxGPRRepr :: NR.NatRepr MaxGPR
maxGPRRepr = NR.knownNat

maxSIMDRepr :: NR.NatRepr MaxSIMD
maxSIMDRepr = NR.knownNat


-- FIXME: move
forSome :: Some f -> (forall tp . f tp -> r) -> r
forSome (Some x) f = f x

simpleGlobals' :: Some (Assignment Global)
simpleGlobals' =
  Some $ Ctx.empty
  -- meta-state indicating abnormal execution status
  :> bool "__AssertionFailure"
  :> bool "__UndefinedBehavior"
  :> bool "__UnpredictableBehavior"
  :> bool "__EndOfInstruction"
  -- meta-state reifying information about this encoding
  :> int "__ThisInstrEnc"
  :> bv @32 "__ThisInstr"
  -- tracking updates to the program counter
  :> bool "__BranchTaken"
  -- tracking additional execution flags
  :> bool "__PendingInterrupt"
  :> bool "__PendingPhysicalSError"
  :> bool "__Sleeping"
  
  :> bool "__conditionPassed"
  :> bv @4 "__currentCond"   
  :> bv @32 "_PC"
  -- rest of the processor state is unconstrained
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
  forSome allGPRsGlobal $ \allGPRsGlobal' ->
  forSome allSIMDsGlobal $ \allSIMDsGlobal' ->
  Some $ simpleGlobals''
  -- the registers
  :> allGPRsGlobal'
  :> allSIMDsGlobal'
  :> memoryGlobal

-- | All 'Global's with GPRs and SIMDs expanded.
flatTrackedGlobals' :: Some (Assignment Global)
flatTrackedGlobals' =
  forSome simpleGlobals' $ \simpleGlobals'' ->
  forSome gprGlobals' $ \gprGlobals'' ->
  forSome simdGlobals' $ \simdGlobals' ->
  Some $
  (simpleGlobals''
  <++> gprGlobals''
  <++> simdGlobals') :> memoryGlobal

memoryGlobal :: Global MemoryBaseType
memoryGlobal =
  def "__Memory" (WI.BaseArrayRepr (empty :> WI.BaseBVRepr (WI.knownNat @32))
    (WI.BaseBVRepr (WI.knownNat @8))) domainUnbounded

gprGlobals' :: Some (Assignment Global)
gprGlobals' = Ctx.fromList $ map mkReg [0..14]
  where
    mkReg :: Integer -> Some (Global)
    mkReg i = Some $ Global ("GPR" <> T.pack (show i)) (WI.BaseBVRepr (NR.knownNat @32)) domainUnbounded (Just ("GPR"))

allGPRsGlobal :: Some Global
allGPRsGlobal = case gprGlobals' of
  Some asn -> Some $ Global "GPRS" (WI.BaseStructRepr (FC.fmapFC gbType asn)) domainUnbounded Nothing

simdGlobals' :: Some (Assignment Global)
simdGlobals' = Ctx.fromList $ map mkReg [0..31]
  where
    mkReg :: Integer -> Some (Global)
    mkReg i = Some $ Global ("SIMD" <> T.pack (show i)) (WI.BaseBVRepr (NR.knownNat @128)) domainUnbounded (Just ("SIMD"))

allSIMDsGlobal :: Some Global
allSIMDsGlobal = case simdGlobals' of
  Some asn -> Some $ Global "SIMDS" (WI.BaseStructRepr (FC.fmapFC gbType asn)) domainUnbounded Nothing

def :: T.Text -> WI.BaseTypeRepr tp -> GlobalDomain tp -> Global tp
def nm repr dom = Global nm repr dom Nothing

noval :: T.Text -> Global (WI.BaseStructType EmptyCtx)
noval nm = def nm WI.knownRepr domainUnbounded

intarraybv :: forall n. 1 <= n
           => KnownNat n
           => T.Text -> Global (WI.BaseArrayType (EmptyCtx ::> WI.BaseIntegerType) (WI.BaseBVType n))
intarraybv nm = def nm WI.knownRepr domainUnbounded

int :: T.Text -> Global WI.BaseIntegerType
int nm = def nm WI.BaseIntegerRepr domainUnbounded

bool :: T.Text -> Global WI.BaseBoolType
bool nm = def nm WI.BaseBoolRepr domainUnbounded

bv :: forall n. 1 <= n => KnownNat n => T.Text -> Global (WI.BaseBVType n)
bv nm = def nm (WI.BaseBVRepr WI.knownNat) domainUnbounded

bvsingle :: forall n. 1 <= n => KnownNat n => T.Text -> Integer -> Global (WI.BaseBVType n)
bvsingle nm i = def nm WI.knownRepr (domainSingleton (WI.ConcreteBV WI.knownNat i))

bvbits :: forall n. 1 <= n => KnownNat n => String -> T.Text -> Global (WI.BaseBVType n)
bvbits bits nm  =
  if fromIntegral (length bits) == (WI.intValue $ WI.knownNat @n) then
    def nm WI.knownRepr
      (domainSingleton (WI.ConcreteBV WI.knownNat (bitsToInteger $ parseBits bits)))
  else error $ "Bad bits: " ++ show bits

noflag :: T.Text -> Global WI.BaseBoolType
noflag nm = def nm WI.BaseBoolRepr (domainSingleton (WI.ConcreteBool False))

parseBits :: String -> [Bool]
parseBits bits = case bits of
  ('0' : rest) -> False : parseBits rest
  ('1' : rest) -> True : parseBits rest
  [] -> []
  s -> error $ "bad bitstring: " ++ show s

untrackedGlobals' :: Some (Assignment Global)
untrackedGlobals' = Some $ empty
  -- the debug flag should not be set
  :> bvsingle @1 "PSTATE_D" 0
   -- processor mode should always be M32_User
  :> bvbits @5 "10000" "PSTATE_M"
  -- memory model
  :> noflag "__ExclusiveLocal"
  -- this flag is set but never read
  :> noflag "ShouldAdvanceIT"
  -- this is initialized before it is read, so we don't need to track it
  :> intarraybv @64 "_Dclone"
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
  :> bv @32 "FPSCR"
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
