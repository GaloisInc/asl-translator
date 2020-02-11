{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
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
  ( trackedGlobals'
  , untrackedGlobals'
  ) where

import           GHC.Natural ( naturalFromInteger )

import           Control.Applicative ( Const(..) )
import           Control.Monad ( forM, foldM )
import           Control.Monad.Except ( throwError )
import qualified Control.Monad.Except as ME

import           GHC.TypeNats ( KnownNat )
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.Ctx ( type (<+>) )
import           Data.Parameterized.Context ( EmptyCtx, (::>), Assignment, empty, pattern (:>) )
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

trackedGlobals' :: Some (Assignment Global)
trackedGlobals' = Some $ empty
  -- meta-state indicating abnormal execution status
  :> bool "__AssertionFailure"
  :> bool "__UndefinedBehavior"
  :> bool "__UnpredictableBehavior"
  -- tracking updates to the program counter
  :> bool "__BranchTaken"
  :> bv @32 "_PC"
  -- the register state, represented as an array indexed by 4-bit bitvectors with 32-bit values
  :> def "_Rbv" (WI.BaseArrayRepr (empty :> WI.BaseBVRepr (WI.knownNat @4))
                  (WI.BaseBVRepr (WI.knownNat @32))) domainUnbounded
  -- the processor state. We assume always user mode
  :> bvbits @5 "10000" "PSTATE_M"

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


def :: T.Text -> WI.BaseTypeRepr tp -> GlobalDomain tp -> Global tp
def nm repr dom = Global nm repr dom

bool :: T.Text -> Global WI.BaseBoolType
bool nm = def nm WI.BaseBoolRepr domainUnbounded

bv :: forall n. 1 <= n => KnownNat n => T.Text -> Global (WI.BaseBVType n)
bv nm = def nm (WI.BaseBVRepr WI.knownNat) domainUnbounded

bvsingle :: forall n. 1 <= n => KnownNat n => T.Text -> Integer -> Global (WI.BaseBVType n)
bvsingle nm i = def nm (WI.BaseBVRepr WI.knownNat) (domainSingleton (WI.ConcreteBV WI.knownNat i))

bvbits :: forall n. 1 <= n => KnownNat n => String -> T.Text -> Global (WI.BaseBVType n)
bvbits bits nm  =
  if fromIntegral (length bits) == (WI.intValue $ WI.knownNat @n) then
    def nm (WI.BaseBVRepr WI.knownNat)
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
  -- :> bvbits @5 "10000" "PSTATE_M"
  -- memory model
  :> noflag "__ExclusiveLocal"
  -- this flag is set but never read
  :> noflag "ShouldAdvanceIT"

  -- system registers
  :> bv @1 "EventRegister"
  :> bv @1 "DBGEN"
  :> bv @1 "SPIDEN"
  :> bv @64 "HCR_EL2"

  :> bv @32 "LR_mon"
  :> bv @32 "DBGOSDLR"
  :> bv @32 "DBGOSLSR"
  :> bv @32 "DBGPRCR"
  :> bv @32 "DBGPRCR_EL1"
  :> bv @32 "EDSCR"
  :> bv @32 "HCR"
  :> bv @32 "HDCR"
  :> bv @32 "HSCTLR"
  :> bv @32 "MDSCR_EL1"
  :> bv @32 "MDCR_EL2"
  :> bv @32 "MDCR_EL3"
  :> bv @32 "OSDLR_EL1"
  :> bv @32 "OSLSR_EL1"
  :> bv @32 "SCR"
  :> bv @32 "SCR_EL3"
  :> bv @32 "SCTLR"
  :> bv @32 "SDCR"
  :> bv @32 "SDER"
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
