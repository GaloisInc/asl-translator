{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Language.ASL.Crucible.Extension (
    ASLExt
  , ASLApp(..)
  , ASLStmt(..)
  , SymFnWrapper(..)
  , SymFnEnv
  , UFFreshness(..)
  , aslExtImpl
  ) where

import qualified Control.Exception as X
import           Control.Lens ( (^.), (&), (.~) )
import           Control.Monad ( guard )
import           Data.IORef
import           Data.Maybe ( isNothing )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as T
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Extension as CCExt
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.ExecutionTree as CSET
import qualified Lang.Crucible.Simulator.Evaluation as CSE
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified Lang.Crucible.Simulator.RegValue as CSR
import qualified Lang.Crucible.Types as CT
import qualified Prettyprinter as PP
import qualified What4.BaseTypes as WT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import           Language.ASL.Crucible.Exceptions ( CrucibleException(..) )
import           Language.ASL.Signature ( BaseGlobalVar(..) )
import           Language.ASL.Types

-- NOTE: Translate calls (both expr and stmt) as What4 uninterpreted functions
--
-- Actually, might even need an extension to represent this properly, since we don't want an actual
-- call.  The return value of the EvalAppFunc is a RegValue (which can be a SymExpr -- a What4 UF).

-- | A language extension for the ASL translation
--
-- Currently, it has no parameters, but we might need to add one if there are arch-specific
-- extensions required later.
--
-- The main reason we need this is in translating calls, which we need to keep as uninterpreted.  It
-- doesn't seem like we can represent that directly in Crucible; this allows us to translate
-- uninterpreted functions into UFs directly in What4.
data ASLExt arch

data UFFreshness = UFFresh | UFCached
  deriving (Show, Eq, Ord)

data ASLApp f tp where
  UF :: T.Text
     -> UFFreshness
     -> WT.BaseTypeRepr rtp
     -> Ctx.Assignment CT.TypeRepr tps
     -> Ctx.Assignment f tps
     -> ASLApp f (CT.BaseToType rtp)
  GetBaseStruct :: CT.TypeRepr (CT.SymbolicStructType ctx)
                -> Ctx.Index ctx tp
                -> f (CT.SymbolicStructType ctx)
                -> ASLApp f (CT.BaseToType tp)
  MkBaseStruct :: Ctx.Assignment CT.TypeRepr ctx
               -> Ctx.Assignment f ctx
               -> ASLApp f (CT.SymbolicStructType (ToBaseTypes ctx))
  -- SetBaseStruct :: Ctx.Assignment CT.TypeRepr ctx
  --               -> f (CT.SymbolicStructType (ToBaseTypes ctx))
  --               -> Ctx.Index ctx tp
  --               -> f tp
  --               -> ASLApp f (CT.SymbolicStructType (ToBaseTypes ctx))

-- | The statement extension type
--
-- These forms must be statements because only statements have access to the
-- solver state
data ASLStmt arch f tp where
  GetRegState :: Ctx.Assignment WT.BaseTypeRepr regs
              -> Ctx.Assignment BaseGlobalVar regs
              -> ASLStmt arch f (CT.SymbolicStructType regs)
  SetRegState :: Ctx.Assignment BaseGlobalVar regs
              -> f (CT.SymbolicStructType regs)
              -> ASLStmt arch f CT.UnitType


data SymFnWrapper sym where
  SymFnWrapper ::
    WI.SymFn sym args ret -> Ctx.Assignment WT.BaseTypeRepr args -> WT.BaseTypeRepr ret -> SymFnWrapper sym

type SymFnEnv sym = Map T.Text (SymFnWrapper sym)

-- | The ASLExt app evaluator
-- | The ASLExt app evaluator
aslAppEvalFunc :: forall sym bak arch proxy p ext rtp blocks r ctx
                . (CB.IsSymBackend sym bak)
               => proxy arch
               -> IORef (SymFnEnv sym)
               -> bak
               -> CS.IntrinsicTypes sym
               -> (Int -> String -> IO ())
               -> CS.CrucibleState p sym ext rtp blocks r ctx
               -> CSE.EvalAppFunc sym ASLApp
aslAppEvalFunc _ funsref bak _ _ _ = \evalApp app ->
  let sym = CB.backendGetSym bak in
  case app of
    UF name fresh trep argTps args -> do
      case WS.userSymbol (T.unpack name) of
        Left _err -> X.throw (InvalidFunctionName name)
        Right funcSymbol -> do
          baseArgs <- FC.fmapFC (unSE @sym) <$> extractBase' (\v -> CS.RV <$> evalApp v) argTps args
          let baseTps = toBaseTypes argTps
          funmap <- readIORef funsref
          symFn <- case Map.lookup name funmap of
            Just (SymFnWrapper symFn baseTps' trep')
              | Just Refl <- testEquality baseTps baseTps'
              , Just Refl <- testEquality trep trep'
              , UFCached <- fresh -> do
                return symFn
            x | isNothing x || fresh == UFFresh -> do
              symFn <- WI.freshTotalUninterpFn sym funcSymbol baseTps trep
              modifyIORef funsref (Map.insert name (SymFnWrapper symFn baseTps trep))
              return symFn
            _ -> X.throw $ BadUninterpretedFunctionCache name
          WI.applySymFn sym symFn baseArgs
    GetBaseStruct _srep idx term -> do
      rv <- evalApp term
      WI.structField sym rv idx
    MkBaseStruct reprs mems -> do
      evalMems <- extractBase' (\v -> CS.RV <$> evalApp v) reprs mems
      let evalMems' = FC.fmapFC (unSE @sym) evalMems
      WI.mkStruct sym evalMems'


aslStmtEvalFunc :: forall arch sym tp p rtp blocks r ctx
                 . ASLStmt arch (CS.RegEntry sym) tp
                -> CS.CrucibleState p sym (ASLExt arch) rtp blocks r ctx
                -> IO (CSR.RegValue sym tp, CS.CrucibleState p sym (ASLExt arch) rtp blocks r ctx)
aslStmtEvalFunc stmt ctx =
  case stmt of
    GetRegState _reps bvs -> CS.ctxSolverProof (ctx ^. CS.stateContext) $ do
      let sym = ctx ^. CS.stateContext . CS.ctxSymInterface
      let fr = ctx ^. (CSET.stateTree . CSET.actFrame)
      let globals = fr ^. CSET.gpGlobals
      gvals <- FC.traverseFC (readBaseGlobal globals) bvs
      struct <- WI.mkStruct sym gvals
      return (struct, ctx)
    SetRegState (bvs :: Ctx.Assignment BaseGlobalVar regs) vals -> CS.ctxSolverProof (ctx ^. CS.stateContext) $ do
      let sym = ctx ^. CS.stateContext . CS.ctxSymInterface
      let fr = ctx ^. (CSET.stateTree . CSET.actFrame)
      let globals = fr ^. CSET.gpGlobals
      let updateGlobal :: forall tp' . IO (CSG.SymGlobalState sym) -> Ctx.Index regs tp' -> IO (CSG.SymGlobalState sym)
          updateGlobal mgs idx =
            case bvs Ctx.! idx of
              BaseGlobalVar gv -> do
                gs <- mgs
                let rv = CS.regValue vals
                val <- WI.structField sym rv idx
                return (CSG.insertGlobal gv val gs)
      globals' <- Ctx.forIndex (Ctx.size bvs) updateGlobal (pure globals)
      return ((), ctx & CSET.stateTree . CSET.actFrame . CSET.gpGlobals .~ globals')


readBaseGlobal :: (Monad m)
               => CS.SymGlobalState sym
               -> BaseGlobalVar tp
               -> m (WI.SymExpr sym tp)
readBaseGlobal gs (BaseGlobalVar gv) =
  case CSG.lookupGlobal gv gs of
    Nothing -> error ("Unbound global register: " ++ show gv)
    Just rv -> return rv

-- | A wrapper around 'WI.SymExpr' because it is a type family and not injective
data SymExpr' sym tp = SE { unSE :: WI.SymExpr sym tp }

extractBase' :: WI.IsExprBuilder sym
             => (forall tp . f tp -> IO (CS.RegValue' sym tp))
             -> Ctx.Assignment CT.TypeRepr tps
             -> Ctx.Assignment f tps
             -> IO (Ctx.Assignment (SymExpr' sym) (ToBaseTypes tps))
extractBase' evalExpr tps asgn = case (tps, asgn) of
  (Ctx.Empty, Ctx.Empty) -> return Ctx.Empty
  (reprs Ctx.:> repr, vals Ctx.:> val) -> do
    rst <- extractBase' evalExpr reprs vals
    case CT.asBaseType repr of
      CT.NotBaseType -> X.throwIO (ExpectedBaseTypeRepr repr)
      CT.AsBaseType _brepr -> do
        CS.RV se <- evalExpr val
        return $ rst Ctx.:> SE se

type instance CCExt.ExprExtension (ASLExt arch) = ASLApp
type instance CCExt.StmtExtension (ASLExt arch) = ASLStmt arch

instance CCExt.IsSyntaxExtension (ASLExt arch)

aslExtImpl :: forall arch p sym . IORef (SymFnEnv sym) -> CS.ExtensionImpl p sym (ASLExt arch)
aslExtImpl funsref =
  CS.ExtensionImpl { CS.extensionEval = aslAppEvalFunc (Proxy @arch) funsref
                   , CS.extensionExec = aslStmtEvalFunc
                   }


instance FC.FunctorFC (ASLStmt arch) where
  fmapFC f a =
    case a of
      GetRegState reps gvs -> GetRegState reps gvs
      SetRegState gvs s -> SetRegState gvs (f s)

instance FC.FoldableFC (ASLStmt arch) where
  foldrFC _f seed a =
    case a of
      GetRegState _ _ -> seed
      SetRegState _ _ -> seed

instance FC.TraversableFC (ASLStmt arch) where
  traverseFC f a =
    case a of
      GetRegState reps gvs -> pure (GetRegState reps gvs)
      SetRegState gvs s -> SetRegState gvs <$> f s

instance CCExt.TypeApp (ASLStmt arch) where
  appType a =
    case a of
      GetRegState reps _ -> CT.baseToType (WT.BaseStructRepr reps)
      SetRegState _ _ -> CT.UnitRepr

instance CCExt.PrettyApp (ASLStmt arch) where
  ppApp pp a =
    case a of
      GetRegState _reps regs ->
        PP.hsep [ PP.pretty "GetRegState"
                , PP.brackets (PP.cat (PP.punctuate PP.comma (FC.toListFC (PP.pretty . showF) regs)))
                ]
      SetRegState gvs vs ->
        PP.hsep [ PP.pretty "SetRegState"
                , PP.brackets (PP.cat (PP.punctuate PP.comma (FC.toListFC (PP.pretty . showF) gvs)))
                , PP.comma
                , PP.brackets (pp vs)
                ]


instance FC.FunctorFC ASLApp where
  fmapFC f a =
    case a of
      UF name fresh trep argReps vals -> UF name fresh trep argReps (FC.fmapFC f vals)
      GetBaseStruct rep i t -> GetBaseStruct rep i (f t)
      MkBaseStruct rep mems -> MkBaseStruct rep (FC.fmapFC f mems)

instance FC.FoldableFC ASLApp where
  foldrFC f seed a =
    case a of
      UF _ _ _ _ vals -> FC.foldrFC f seed vals
      GetBaseStruct _ _ t -> f t seed
      MkBaseStruct _ mems -> FC.foldrFC f seed mems

instance FC.TraversableFC ASLApp where
  traverseFC f a =
    case a of
      UF name fresh trep argReps vals -> UF name fresh trep argReps <$> FC.traverseFC f vals
      GetBaseStruct rep i t -> GetBaseStruct rep i <$> f t
      MkBaseStruct rep mems -> MkBaseStruct rep <$> FC.traverseFC f mems

instance CCExt.TypeApp ASLApp where
  appType a =
    case a of
      UF _ _ trep _ _ -> CT.baseToType trep
      GetBaseStruct (CT.SymbolicStructRepr reprs) i _ -> CT.baseToType (reprs Ctx.! i)
      MkBaseStruct reprs _ -> CT.SymbolicStructRepr (toBaseTypes reprs)

instance CCExt.PrettyApp ASLApp where
  ppApp pp a =
    case a of
      UF name fresh trep argReps vals ->
        PP.hsep [ PP.pretty name
               , PP.viaShow fresh
               , PP.viaShow trep
               , PP.brackets (PP.cat (PP.punctuate PP.comma (FC.toListFC (PP.pretty . showF) argReps)))
               , PP.brackets (PP.cat (PP.punctuate PP.comma (FC.toListFC pp vals)))
               ]
      GetBaseStruct _r i t ->
        PP.hsep [ PP.pretty "GetBaseStruct"
                , PP.pretty (showF i)
                , pp t
                ]
      MkBaseStruct _r _mems ->
        PP.hsep [ PP.pretty "MkBaseStruct"
                , PP.pretty "PP UNIMPLEMENTED"
                ]

instance FC.TestEqualityFC ASLApp where
  testEqualityFC testFC a1 a2 =
    case (a1, a2) of
      (UF n1 f1 r1 rs1 vs1, UF n2 f2 r2 rs2 vs2) -> do
        guard (n1 == n2 && f1 == f2)
        Refl <- testEquality r1 r2
        Refl <- testEquality rs1 rs2
        Refl <- FC.testEqualityFC testFC vs1 vs2
        return Refl
      (GetBaseStruct r1 i1 t1, GetBaseStruct r2 i2 t2) -> do
        Refl <- testEquality r1 r2
        Refl <- testEquality i1 i2
        Refl <- testFC t1 t2
        return Refl
      (MkBaseStruct t1 mems1, MkBaseStruct t2 mems2) -> do
        Refl <- testEquality t1 t2
        Refl <- FC.testEqualityFC testFC mems1 mems2
        return Refl
      _ -> Nothing

instance FC.OrdFC ASLApp where
  compareFC compareTerm a1 a2 =
    case (a1, a2) of
      (UF n1 f1 r1 rs1 vs1, UF n2 f2 r2 rs2 vs2) ->
        case compare n1 n2 of
          LT -> LTF
          GT -> GTF
          EQ -> case compare f1 f2 of
            LT -> LTF
            GT -> GTF
            EQ -> case compareF r1 r2 of
              LTF -> LTF
              GTF -> GTF
              EQF -> case compareF rs1 rs2 of
                LTF -> LTF
                GTF -> GTF
                EQF -> case FC.compareFC compareTerm vs1 vs2 of
                  LTF -> LTF
                  GTF -> GTF
                  EQF -> EQF
      (GetBaseStruct r1 i1 t1, GetBaseStruct r2 i2 t2) ->
        case compareF r1 r2 of
          LTF -> LTF
          GTF -> GTF
          EQF -> case compareF i1 i2 of
            LTF -> LTF
            GTF -> GTF
            EQF -> case compareTerm t1 t2 of
              LTF -> LTF
              GTF -> GTF
              EQF -> EQF
      (MkBaseStruct t1 mems1, MkBaseStruct t2 mems2) ->
        case compareF t1 t2 of
          LTF -> LTF
          GTF -> GTF
          EQF -> case FC.compareFC compareTerm mems1 mems2 of
            LTF -> LTF
            GTF -> GTF
            EQF -> EQF
      (UF {}, _) -> LTF
      (GetBaseStruct {}, MkBaseStruct {}) -> LTF
      (GetBaseStruct {}, _) -> GTF
      (MkBaseStruct {}, _) -> GTF
