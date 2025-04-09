{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}

module Language.ASL (
    simulateFunction
  , simulateInstruction
  , SimulatorConfig(..)
  , SimulationException(..)
  ) where

import           Data.IORef
import qualified Control.Exception as X
import           Control.Lens ( (^.) )
import           Control.Applicative ( Const(..) )
import qualified Control.Monad.Fail as MF
import qualified Control.Monad.Identity as I
import           Control.Monad ( liftM, unless )
import qualified Control.Monad.ST as ST
import qualified Data.HashTable.Class as H

import qualified Data.Map as Map
import           Data.Time.Clock
import           Data.Parameterized.Pair ( Pair(..) )
import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Text as T
import           Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Maybe ( catMaybes )

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.CallFrame as CSC
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator.PathSatisfiability as CSP
import qualified System.IO as IO
import qualified What4.Config as WC
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS
import qualified What4.Protocol.Online as WPO

import qualified What4.Expr as S

-- import qualified Dismantle.Formula as SF
import qualified Language.ASL.Crucible as AC
import qualified Language.ASL.Crucible.Extension as AE

import qualified Language.ASL.Signature as AS
import qualified Language.ASL.Types as AT
import qualified Language.ASL.Globals as G

import qualified Prettyprinter as LPP
import qualified Prettyprinter.Render.String as LPP
import qualified Text.PrettyPrint.HughesPJClass as PP

data SimulatorConfig scope =
  SimulatorConfig { simOutputHandle :: IO.Handle
                  , simHandleAllocator :: CFH.HandleAllocator
                  , simBackend :: CBO.YicesOnlineBackend scope S.EmptyExprBuilderState (S.Flags S.FloatReal)
                  }

type IsSym scope sym = sym ~ S.ExprBuilder scope S.EmptyExprBuilderState (S.Flags S.FloatReal)

freshRegEntries :: Ctx.Assignment (FreshArg sym) btps -> Ctx.Assignment (CS.RegEntry sym) (AT.ToCrucTypes btps)
freshRegEntries Ctx.Empty = Ctx.Empty
freshRegEntries (fargs Ctx.:> farg) = (freshRegEntries fargs Ctx.:> (freshArgEntry farg))

genSimulation :: forall arch sym init innerReads innerWrites outerReads outerWrites tps scope a
               . IsSym scope sym
              => SimulatorConfig scope
              -> AC.GenFunction arch innerReads innerWrites outerReads outerWrites init tps
              -> (CS.RegEntry sym (AS.FuncReturn innerWrites tps)
                  -> Ctx.Assignment (WI.BoundVar sym) init
                  -> WI.BoundVar sym (WT.BaseStructType outerReads)
                  -> IO a)
              -> IO a
genSimulation symCfg crucFunc extractResult =
  case AC.funcCFG crucFunc of
    CCC.SomeCFG cfg -> do
      let bak = simBackend symCfg
      let sym = CB.backendGetSym bak
      let sig = AC.funcSig crucFunc
      let argReprNames = FC.fmapFC (\(AT.LabeledValue (AS.FunctionArg nm _) v) -> AT.LabeledValue nm v) (AC.funcArgReprs sig)
      initArgs <- FC.traverseFC (allocateFreshArg sym) argReprNames
      let retRepr = AS.funcSigRepr sig
      let econt = CS.runOverrideSim retRepr $ do
            re <- CS.callCFG cfg (CS.RegMap $ freshRegEntries initArgs)
            return (CS.regValue re)
      let globalReads = AC.funcGlobalReads crucFunc
      let globalReadReprs = FC.fmapFC AT.projectValue (AC.funcOuterReadReprs crucFunc)
      let globalReadStructRepr = WT.BaseStructRepr globalReadReprs
      FreshArg _ gbv <- allocateFreshArg sym (AC.LabeledValue "globalReads" globalReadStructRepr)
      let globalStruct = WI.varExpr sym gbv
      globals <- Ctx.traverseWithIndex (\idx _ -> WI.structField sym globalStruct idx) globalReadReprs
      -- initialize exactly the variables which are both actually read (i.e. "inner") and appear
      -- in the outer signature of this function (i.e "outer").
      -- inner variables which do not appear in the outer signature are assumed to be undefined,
      -- and currently this is handled by the translator itself, using its own facility for
      -- instantiating undefined vlaues.
      Pair globalsInitEs globalsInitVars <-
        return $ extractSubCtx (AC.funcReadProj crucFunc) globals globalReads

      let globalState = initGlobals symCfg globalsInitEs globalsInitVars
      (s0, _) <- initialSimulatorState symCfg globalState econt retRepr
      ft <- executionFeatures (AS.funcName $ AC.funcSig crucFunc) bak
      let onlineDisabled = MF.fail "`concretize` requires online solving to be enabled"
      CBO.withSolverProcess bak onlineDisabled $ \p -> do
        let argBVs = FC.fmapFC freshArgBoundVar initArgs
        let allBVs = getBVs initArgs ++ [Some gbv]
        eres <- WPO.inNewFrameWithVars p allBVs $ do
          CS.executeCrucible ft s0
        case eres of
          CS.TimeoutResult {} -> X.throwIO (SimulationTimeout (Some (AC.SomeFunctionSignature sig)))
          CS.AbortedResult _ ab -> X.throwIO $ SimulationAbort (Some (AC.SomeFunctionSignature sig)) (showAbortedResult ab)
          CS.FinishedResult _ pres -> do
            gp <- case pres of
              CS.TotalRes gp -> return gp
              CS.PartialRes _ _ gp _ -> return gp
            extractResult (gp ^. CS.gpValue) argBVs gbv
  where
    getBVs ctx = FC.toListFC (\(FreshArg _ bv) -> Some bv) ctx

extractSubCtx :: forall f g outer inner
               . (forall tp. Ctx.Index outer tp -> Maybe (Ctx.Index inner tp))
              -> Ctx.Assignment f outer
              -> Ctx.Assignment g inner
              -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
extractSubCtx idxMap asnf asng = I.runIdentity $ do
  asnpaired <- Ctx.traverseWithIndex getVal asnf
  return $ pairToCtxs $ catMaybes $ FC.toListFC (\(Const v) -> v) $ asnpaired
  where
    getVal :: forall tp. Ctx.Index outer tp -> f tp -> I.Identity (Const (Maybe (Pair f g)) tp)
    getVal idx f = case idxMap idx of
      Just gidx -> return $ Const $ Just (Pair f (asng Ctx.! gidx))
      Nothing -> return $ Const Nothing

pairToCtxs :: [Pair f g] -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
pairToCtxs = go Ctx.empty Ctx.empty
  where go :: Ctx.Assignment f ctx -> Ctx.Assignment g ctx -> [Pair f g] -> Pair (Ctx.Assignment f) (Ctx.Assignment g)
        go fs gs [] = Pair fs gs
        go fs gs (Pair f g : next) = ((go $! (fs `Ctx.extend` f)) $! (gs `Ctx.extend` g)) next

-- | Simulate a function
--
-- We have to maintain the mapping between exprs and the global
-- location (i.e., register or memory) that is being updated by the function.  This is also
-- suitable for the top-level instruction semantics, which operate in the same way (but take no
-- arguments)
simulateFunction :: forall arch sym init globalReads globalWrites tps scope
                  . IsSym scope sym
                 => SimulatorConfig scope
                 -> AC.Function arch globalReads globalWrites init tps
                 -> IO (S.ExprSymFn scope (init Ctx.::> WT.BaseStructType globalReads) (WT.BaseStructType (AS.FuncReturnCtx globalWrites tps)))
simulateFunction symCfg crucFunc = genSimulation symCfg crucFunc extractResult
  where
    sig = AC.funcSig crucFunc
    bak = simBackend symCfg
    sym = CB.backendGetSym bak

    retType = AS.funcSigBaseRepr sig

    extractResult re argBVs globalBV =
      case CT.asBaseType (CS.regType re) of
        CT.NotBaseType -> X.throwIO (NonBaseTypeReturn (CS.regType re))
        CT.AsBaseType btr
          | Just Refl <- testEquality btr retType -> do
              let name = T.unpack (AS.funcName sig)
                  solverSymbolName = WI.safeSymbol name
              let allArgBvs = (argBVs Ctx.:> globalBV)
              fn <- WI.definedFn
                sym
                solverSymbolName
                allArgBvs
                (CS.regValue re)
                WI.NeverUnfold
              checkClosedTerm allArgBvs (CS.regValue re)

              return $ fn
          | otherwise -> X.throwIO (UnexpectedReturnType btr)


simulateInstruction :: forall arch sym init globalReads globalWrites scope
                     . IsSym scope sym
                    => SimulatorConfig scope
                    -> AC.Instruction arch globalReads globalWrites init
                    -> IO (S.ExprSymFn scope (init Ctx.::> WT.BaseStructType G.StructGlobalsCtx) (WT.BaseStructType G.StructGlobalsCtx))
simulateInstruction symCfg crucFunc = genSimulation symCfg crucFunc extractResult
  where
    sig = AC.funcSig crucFunc
    bak = simBackend symCfg
    sym = CB.backendGetSym bak

    retType = AS.funcSigBaseRepr sig

    mkStructField :: WI.SymExpr sym (WT.BaseStructType G.StructGlobalsCtx)
                  -> WI.SymExpr sym (WT.BaseStructType globalWrites)
                  -> Ctx.Index G.StructGlobalsCtx tp
                  -> IO (WI.SymExpr sym tp)
    mkStructField inStruct outStruct idx = case AC.funcWriteProj crucFunc idx of
      Just idx' -> WI.structField sym outStruct idx'
      -- global is not written to, so it passes through unmodified
      Nothing -> WI.structField sym inStruct idx

    extractResult re argBVs globalBV =
      case CT.asBaseType (CS.regType re) of
        CT.NotBaseType -> X.throwIO (NonBaseTypeReturn (CS.regType re))
        CT.AsBaseType btr
          | Just Refl <- testEquality btr retType -> do
              let name = T.unpack (AS.funcName sig)
                  solverSymbolName = WI.safeSymbol name
              let allArgBvs = (argBVs Ctx.:> globalBV)
              let globalRead = WI.varExpr sym globalBV
              innerStruct <- WI.structField sym (CS.regValue re) Ctx.i1of2
              result <- Ctx.traverseWithIndex (\idx _ -> mkStructField globalRead innerStruct idx) G.trackedGlobalReprs
              finalStruct <- WI.mkStruct sym result
              fn <- WI.definedFn
                sym
                solverSymbolName
                allArgBvs
                finalStruct
                WI.NeverUnfold
              checkClosedTerm allArgBvs finalStruct
              return $ fn
          | otherwise -> X.throwIO (UnexpectedReturnType btr)

checkClosedTerm :: forall scope sym ctx tp
                 . IsSym scope sym
                => Ctx.Assignment (WI.BoundVar sym) ctx
                -> WI.SymExpr sym tp
                -> IO ()
checkClosedTerm allBvs expr = do
  bvs <- liftM (Set.unions . map snd) $ ST.stToIO $ H.toList =<< S.boundVars expr
  let allbvs = Set.fromList $ V.toList $ Ctx.toVector allBvs Some
  unless (bvs `Set.isSubsetOf` allbvs) $
    X.throwIO $ UnexpectedBoundVars @scope allbvs bvs expr

data FreshArg sym bt = FreshArg { freshArgEntry :: CS.RegEntry sym (CT.BaseToType bt)
                                , freshArgBoundVar :: WI.BoundVar sym bt
                                }

type family ToCrucTypes (wtps :: CT.Ctx WT.BaseType) :: CT.Ctx CT.CrucibleType where
  ToCrucTypes CT.EmptyCtx = CT.EmptyCtx
  ToCrucTypes (wtps CT.::> wtp) = ToCrucTypes wtps CT.::> CT.BaseToType wtp


allocateFreshArg :: IsSym scope sym
                 => sym
                 -> AC.LabeledValue T.Text CT.BaseTypeRepr btp
                 -> IO (FreshArg sym btp)
allocateFreshArg sym (AC.LabeledValue name rep) = do
  case rep of
    CT.BaseBVRepr w -> do
      sname <- toSolverSymbol (T.unpack name)
      bv <- WI.freshBoundVar sym sname (WT.BaseBVRepr w)
      return $ FreshArg
        ( CS.RegEntry { CS.regType = CT.baseToType rep
                      , CS.regValue = WI.varExpr sym bv
                      } )
        bv
    CT.BaseIntegerRepr -> do
      sname <- toSolverSymbol (T.unpack name)
      bv <- WI.freshBoundVar sym sname WT.BaseIntegerRepr
      return $ FreshArg
        ( CS.RegEntry { CS.regType = CT.baseToType rep
                      , CS.regValue = WI.varExpr sym bv
                      } )
        bv
    CT.BaseBoolRepr -> do
      sname <- toSolverSymbol (T.unpack name)
      bv <- WI.freshBoundVar sym sname WT.BaseBoolRepr
      return $ FreshArg
        ( CS.RegEntry { CS.regType = CT.baseToType rep
                      , CS.regValue = WI.varExpr sym bv
                      } )
        bv
    CT.BaseArrayRepr idxTy vTy -> do
      sname <- toSolverSymbol (T.unpack name)
      bv <- WI.freshBoundVar sym sname (WT.BaseArrayRepr idxTy vTy)
      return $ FreshArg
        ( CS.RegEntry { CS.regType = CT.baseToType rep
                      , CS.regValue = WI.varExpr sym bv
                      } )
        bv
    CT.BaseStructRepr idxTy -> do
      sname <- toSolverSymbol (T.unpack name)
      bv <- WI.freshBoundVar sym sname (WT.BaseStructRepr idxTy)
      return $ FreshArg
        ( CS.RegEntry { CS.regType = CT.baseToType rep
                      , CS.regValue = WI.varExpr sym bv
                      } )
        bv
    _ -> X.throwIO (CannotAllocateFresh name rep)

toSolverSymbol :: String -> IO WS.SolverSymbol
toSolverSymbol s' =
  let s = case s' of '_' : rst -> "UU_" ++ rst
                     _ -> s'
  in case WS.userSymbol s of
    Right sy -> return sy
    Left _err -> X.throwIO (InvalidSymbolName s)

initialSimulatorState :: IsSym scope sym
                      => SimulatorConfig scope
                      -> CS.SymGlobalState sym
                      -> CS.ExecCont () sym (AC.ASLExt arch) (CS.RegEntry sym ret) (CSC.OverrideLang ret) ('Just CT.EmptyCtx)
                      -> CT.TypeRepr ret
                      -> IO (CS.ExecState () sym (AC.ASLExt arch) (CS.RegEntry sym ret), IORef (AE.SymFnEnv sym))
initialSimulatorState symCfg symGlobalState econt retRepr = do
  let intrinsics = CS.emptyIntrinsicTypes
  let bak = simBackend symCfg
  let hdlAlloc = simHandleAllocator symCfg
  let outputHandle = simOutputHandle symCfg
  funsref <- newIORef (Map.empty :: AE.SymFnEnv sym)
  let bindings = CS.FnBindings CFH.emptyHandleMap
  let simContext = CS.initSimContext bak intrinsics hdlAlloc outputHandle bindings (AC.aslExtImpl funsref) ()
  let hdlr = CS.defaultAbortHandler
  return (CS.InitialState simContext symGlobalState hdlr retRepr econt, funsref)

-- | Allocate all of the globals that will be referred to by the statement
-- sequence (even indirectly) and use them to populate a 'CS.GlobalSymState'
initGlobals :: forall sym env scope
             . IsSym scope sym
            => SimulatorConfig scope
            -> Ctx.Assignment (S.Expr scope) env
            -> Ctx.Assignment AC.BaseGlobalVar env
            -> CS.SymGlobalState sym
initGlobals _ globalExprs globalVars = do
  Ctx.forIndex (Ctx.size globalVars) addGlobal CS.emptyGlobals
  where
    addGlobal :: forall bt
               . CSG.SymGlobalState sym
              -> Ctx.Index env bt
              -> CSG.SymGlobalState sym
    addGlobal gs idx =
      let
        AC.BaseGlobalVar gv = globalVars Ctx.! idx
      in CSG.insertGlobal gv (globalExprs Ctx.! idx) gs

executionFeatures :: IsSym scope sym
                  => WPO.OnlineSolver solver
                  => CCE.IsSyntaxExtension ext
                  => T.Text
                  -> CBO.OnlineBackend solver scope S.EmptyExprBuilderState (S.Flags S.FloatReal)
                  -> IO [CS.ExecutionFeature p sym ext rtp]
executionFeatures nm bak = do
  let sym = CB.backendGetSym bak
  gft <- CSP.pathSatisfiabilityFeature sym (CBO.considerSatisfiability bak)
  -- FIXME: What is the general requirement here?
  let psf = if nm `elem` [ "VLDMDB_A1", "VLDM_A1", "FLDMDBX_A1"
                         , "FLDMIAX_A1", "FSTMDBX_A1", "FSTMIAX_A1"
                         , "VSTMDB_A1", "VSTM_A1"
                         , "VLDMDB_T1", "VLDM_T1", "FLDMDBX_T1"
                         , "FLDMIAX_T1", "FSTMDBX_T1", "FSTMIAX_T1"
                         , "VSTMDB_T1", "VSTM_T1"
                         ]
        then [CS.genericToExecutionFeature gft] else []
  timeout <- CS.genericToExecutionFeature <$> CS.timeoutFeature (2000.00 :: NominalDiffTime)
  let fts = psf ++ [timeout]
  let cfg = WI.getConfiguration sym
  _pathSetter <- WC.getOptionSetting CBO.solverInteractionFile cfg
  -- res <- WC.setOpt pathSetter (T.pack "./output/yices.out")
  -- X.assert (null res) (return fts)
  return fts

data SimulationException = SimulationTimeout (Some AC.SomeFunctionSignature)
                         | SimulationAbort (Some AC.SomeFunctionSignature) T.Text
                         | forall tp . NonBaseTypeReturn (CT.TypeRepr tp)
                         | forall btp . UnexpectedReturnType (WT.BaseTypeRepr btp)
                         | forall tp . MissingGlobalDefinition (CS.GlobalVar tp)
                         | forall tp . CannotAllocateFresh T.Text (CT.BaseTypeRepr tp)
                         | forall sym ret. UnexpectedBoundVars (Set (Some (S.ExprBoundVar sym))) (Set (Some (S.ExprBoundVar sym))) (S.Expr sym ret)
                         | InvalidSymbolName String


instance PP.Pretty SimulationException where
  pPrint e = case e of

    SimulationTimeout (Some fs) -> PP.text "SimulationTimeout:" PP.<+> PP.text (show fs)
    SimulationAbort (Some fs) msg ->
      PP.text "SimulationAbort:" PP.<+> PP.text (T.unpack msg) PP.<+> PP.text (show fs)
    NonBaseTypeReturn tr ->
      PP.text "NonBaseTypeReturn:" PP.<+> PP.text (show tr)
    UnexpectedReturnType btr ->
      PP.text "UnexpectedReturnType:" PP.<+> PP.text (show btr)
    MissingGlobalDefinition gv ->
      PP.text "MissingGlobalDefinition:" PP.<+> PP.text (show gv)
    CannotAllocateFresh nm btr ->
      PP.text "CannotAllocateFresh: " PP.<+> PP.text (T.unpack nm) PP.<+> PP.text (show btr)
    UnexpectedBoundVars bvs1 bvs2 expr ->
      PP.text "UnexpectedBoundVars:"
      PP.$$ (PP.text "Expected:" PP.<+> PP.text (show bvs1) PP.<+> PP.text "Got: " PP.<+> PP.text (show bvs2)
      PP.<+> PP.text "In:")
      PP.$$ showExpr expr
    InvalidSymbolName nm ->
      PP.text "InvalidSymbolName:" PP.<+> PP.text nm

instance Show SimulationException where
  show e = PP.render (PP.pPrint e)

showExpr :: S.Expr t ret -> PP.Doc
showExpr e = PP.text (LPP.renderString (LPP.layoutPretty opts (WI.printSymExpr e)))
  where opts = LPP.LayoutOptions (LPP.AvailablePerLine 80 0.4)

showAbortedResult :: CS.AbortedResult c d -> T.Text
showAbortedResult ar = case ar of
  CS.AbortedExec reason _ -> T.pack $ show reason
  CS.AbortedExit code _ -> T.pack $ show code
  CS.AbortedBranch _ _ res' res'' -> "BRANCH: " <> showAbortedResult res' <> "\n" <> showAbortedResult res''


instance X.Exception SimulationException
