{-|
Module           : Language.ASL.Translation.Driver
Copyright        : (c) Galois, Inc 2019-2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module implements the translation pipeline. Given a
set of translation options, it performs the following steps:

* Read in the pre-parsed ASL specification (from s-expressions).
* Translate each instruction into a Crucible CFG (via "Language.ASL.Translation").
* For each instruction, translate (recursively) any called functions.
* For all translated instructions/functions, symbolically
  execute the Crucible CFG into a What4 function.
* Serialize all resulting What4 functions as s-expressions.

As a separate pass (specified by the translator options),
it also drives the "normalization" of the resulting What4 functions.
In this case, the s-expressions from the translation are read back in,
normalized, then written out again.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

module Language.ASL.Translation.Driver
  ( TranslatorOptions(..)
  , defaultFilePaths
  , defaultOptions
  , TranslationMode(..)
  , SimulationMode(..)
  , NormalizeMode(..)
  , StatOptions(..)
  , defaultStatOptions
  , TranslationDepth(..)
  , FilePathConfig(..)
  , ExpectedException(..)
  , translateAndSimulate
  , SigMap
  , reportStats
  , serializeFormulas
  , readAndNormalize
  ) where

import           GHC.Stack ( HasCallStack )
import qualified GHC.Stack as Ghc

import qualified Control.Exception as X

import qualified Control.Concurrent as IO
import           Control.Concurrent.MVar

import           Control.Monad.Identity
import           Control.Monad (forM_, when)
import qualified Control.Monad.State.Lazy as MSS
import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class
import qualified Control.Monad.Fail as MF

import           Data.Either ( partitionEithers )
import           Data.Map ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Maybe ( catMaybes )
import           Data.Monoid
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Bits( (.|.) )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Language.ASL.Parser as AP
import qualified Language.ASL.Syntax as AS
import           System.Exit (exitFailure)

import qualified Dismantle.ARM.T32 as T32
import qualified Dismantle.ARM.A32 as A32
import qualified Dismantle.ARM.ASL as DA ( Encoding(..) )
import           Dismantle.ARM.ASL ( encodingIdentifier )

import qualified System.IO as IO
import           System.IO (hPutStrLn, stderr)

import qualified Language.ASL.SyntaxTraverse as TR

import qualified Language.ASL as ASL
import qualified Language.ASL.Formulas.Serialize as FS
import qualified Language.ASL.Formulas.Normalize as FS

import qualified Language.ASL.Crucible as AC

import           Language.ASL.Translation.Preprocess
import           Language.ASL.Translation.Exceptions
import           Language.ASL.Signature
import           Language.ASL.StaticExpr

import qualified What4.Expr.Builder as B
import qualified What4.Interface as WI
import qualified What4.Solver.Yices as Yices
import qualified What4.Config as WC
import           What4.ProblemFeatures

import qualified What4.Serialize.Normalize as WN

import qualified Text.PrettyPrint.HughesPJClass as PP
import qualified Text.PrettyPrint.ANSI.Leijen as LPP

import           What4.Utils.Log ( HasLogCfg, LogCfg, withLogCfg )
import qualified What4.Utils.Log as Log
import           What4.Utils.Util ( SomeSome(..) )
import qualified What4.Utils.Util as U
import           Util.Log ( MonadLog(..), logIntToLvl, logMsgStr )

-- | Configuration options controlling translation and simulation
data TranslatorOptions = TranslatorOptions
  { optVerbosity :: Integer
  -- ^ verbosity level of the translator. 0 = silent, 1 = warnings, 2 = info, 3 = debug
  , optTranslationMode :: TranslationMode
  -- ^ mode controlling which instructions are translated
  , optSimulationMode :: SimulationMode
  -- ^ mode controlling which instructions/functions are symbolically executed
  , optCollectAllExceptions :: Bool
  -- ^ if true, all exceptions thrown are collected and reported at the end
  -- if false, unexpected exceptions are thrown
  , optCollectExpectedExceptions :: Bool
  -- ^ if true, expected exceptions thrown are collected and reported at the end
  -- if false, all exceptions are thrown
  , optTranslationDepth :: TranslationDepth
  -- ^ mode controlling if translation should proceed recursively
  , optCheckSerialization :: Bool
  -- ^ if true, serialized functions are deserialized and checked for
  -- equivalence
  , optFilePaths :: FilePathConfig
  -- ^ specification of input/output file paths
  , optLogCfg :: LogCfg
  -- ^ internal log configuration 
  , optParallel :: Bool
  -- ^ if true, execute symbolic simulation for each function on a separate thread
  , optNormalizeMode :: NormalizeMode
  -- ^ mode controlling the normalization of the resulting What4 functions
  }

-- | Configuration specifying the location of both input and output files.
data FilePathConfig = FilePathConfig
  { fpDefs :: FilePath
  , fpInsts :: FilePath
  , fpRegs :: FilePath
  , fpSupport :: FilePath
  , fpExtraDefs :: FilePath
  , fpOutFuns :: FilePath
  , fpOutInstrs :: FilePath
  , fpNormFuns :: FilePath
  , fpNormInstrs :: FilePath
  , fpDataRoot :: FilePath
  }

-- | Configuration options controlling the final report after
-- translation/simulation
data StatOptions = StatOptions
  { reportKnownExceptions :: Bool
  , reportSucceedingInstructions :: Bool
  , reportAllExceptions :: Bool
  , reportKnownExceptionFilter :: ExpectedException -> Bool
  , reportFunctionDependencies :: Bool
  }

-- | Default configuration for file paths
defaultFilePaths :: FilePathConfig
defaultFilePaths = FilePathConfig
  { fpDataRoot = "./data/parsed/"
  , fpDefs = "arm_defs.sexpr"
  , fpInsts = "arm_instrs.sexpr"
  , fpRegs = "arm_regs.sexpr"
  , fpSupport = "support.sexpr"
  , fpExtraDefs = "extra_defs.sexpr"
  , fpOutFuns = "./output/functions.what4"
  , fpOutInstrs = "./output/instructions.what4"
  , fpNormFuns = "./output/functions-norm.what4"
  , fpNormInstrs = "./output/instructions-norm.what4"
  }

-- | Default configuration for translation/simulation
defaultOptions :: Log.LogCfg -> TranslatorOptions
defaultOptions logCfg = TranslatorOptions
  { optVerbosity = 1
  , optTranslationMode = TranslateAArch32
  , optSimulationMode = SimulateAll
  , optCollectAllExceptions = False
  , optCollectExpectedExceptions = True
  , optTranslationDepth = TranslateRecursive
  , optCheckSerialization = False
  , optFilePaths = defaultFilePaths
  , optLogCfg = logCfg
  , optParallel = False
  , optNormalizeMode = NormalizeNone
  }

-- | Default configuration for reporting translation/simulation statistics
defaultStatOptions :: StatOptions
defaultStatOptions = StatOptions
  { reportKnownExceptions = False
  , reportSucceedingInstructions = False
  , reportAllExceptions = False
  , reportKnownExceptionFilter = (\_ -> True)
  , reportFunctionDependencies = False
  }

-- | Flag for specifying the translation depth
data TranslationDepth = TranslateRecursive
                      -- ^ recursively translate all function calls
                      | TranslateShallow
                      -- ^ only translate instructions, don't recurse into function calls

-- | Flag for filtering instructions to be translated
data TranslationMode = TranslateAArch32
                     -- ^ translate all of AArch32
                     | TranslateInstruction (T.Text, T.Text)
                     -- ^ translate a specific instruction/encoding pair

-- | Flag for filtering instructions/functions to be symbolically executed
data SimulationMode = SimulateAll
                    -- ^ simulate all functions/instructions
                    | SimulateFunctions
                    -- ^ simulate only functions
                    | SimulateInstructions
                    -- ^ simulate only instructions
                    | SimulateInstruction (T.Text, T.Text)
                    -- ^ simulate only a specific instruction/encoding pair
                    | SimulateNone
                    -- ^ do not perform any simulation

-- | Flag for controlling the normalization mode
data NormalizeMode = NormalizeAll
                   -- ^ normalize all instructions and functions
                   | NormalizeFunctions
                   -- ^ normalize only functions
                   | NormalizeNone
                   -- ^ do not normalize
 deriving (Eq, Show)

-- | Translate and simulate the ASL specification according to the given
-- 'TranslatorOptions', returning a populated 'SigMap'.
translateAndSimulate :: HasCallStack => TranslatorOptions -> IO (SigMap arch)
translateAndSimulate opts = do
  spec <- getASL opts
  logMsgIO opts 0 $ "Loaded "
    ++ show (length $ aslInstructions spec) ++ " instructions and "
    ++ show (length $ aslDefinitions spec) ++ " definitions and "
    ++ show (length $ aslSupportDefinitions spec) ++ " support definitions and "
    ++ show (length $ aslExtraDefinitions spec) ++ " extra definitions and "
    ++ show (length $ aslRegisterDefinitions spec) ++ " register definitions."
  (sigEnv, sigState) <- buildSigState spec (optLogCfg opts)
  translateAndSimulate' opts spec sigEnv sigState

data BuilderData t = NoBuilderData

-- | Read in an existing specification, perform a normalization pass and
-- then write out the result.
readAndNormalize :: TranslatorOptions -> IO ()
readAndNormalize opts = do
  let
    FilePathConfig { fpOutFuns, fpOutInstrs, fpNormFuns, fpNormInstrs, ..} = optFilePaths opts

  logMsgIO opts 0 $ "Reading functions from: " ++ fpOutFuns
  funsexpr <- T.readFile fpOutFuns >>= FS.parseSExpr
  minstsexpr <- case optNormalizeMode opts of
    NormalizeFunctions -> return Nothing
    _ -> do
      logMsgIO opts 0 $ "Reading instructions from: " ++ fpOutInstrs
      Just <$> (T.readFile fpOutInstrs >>= FS.parseSExpr)
  logMsgIO opts 0 $ "Normalizing formulas.."
  (funsexpr', minstsexpr') <- FS.normalizeSymFnEnv funsexpr minstsexpr

  logMsgIO opts 0 $ "Writing normalized formulas to: " ++ fpNormFuns
  T.writeFile fpNormFuns (FS.printSExpr $ funsexpr')
  case minstsexpr' of
    Just instsexpr' -> do
      logMsgIO opts 0 $ "Writing normalized instructions to: " ++ fpNormInstrs
      T.writeFile fpNormInstrs (FS.printSExpr $ instsexpr')
    Nothing -> return ()

-- | Write out the serialized What4 functions from the given 'SigMap'
-- to their corresponding file path according to the given 'TranslatorOptions'
serializeFormulas :: TranslatorOptions -> SigMap arch -> IO ()
serializeFormulas opts (sFormulaPromises -> promises) = do
  let
    FilePathConfig { fpOutFuns, fpOutInstrs, ..} = optFilePaths opts

  (instrs, funs) <- (partitionEithers . reverse) <$> mapM getFormula promises

  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr NoBuilderData r

  case (optSimulationMode opts) of
    SimulateAll -> do
      fnEnv <- doSerialize sym Map.empty fpOutFuns funs
      void $ doSerialize sym fnEnv fpOutInstrs instrs
    SimulateFunctions ->
      void $ doSerialize sym Map.empty fpOutFuns funs
    SimulateInstructions ->
      void $ doSerialize sym Map.empty fpOutInstrs instrs
    SimulateInstruction _ ->
      void $ doSerialize sym Map.empty fpOutInstrs instrs
    SimulateNone -> return ()
  where
    doSerialize :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                => sym
                -> FS.NamedSymFnEnv sym
                -> FilePath
                -> [FS.SExpr]
                -> IO (FS.NamedSymFnEnv sym)
    doSerialize sym env out sexprs = do
      logMsgIO opts 0 $ "Writing formulas to: " ++ out
      allsexpr <- return $ FS.assembleSymFnEnv sexprs
      txt <- return $ FS.printSExpr $ allsexpr
      T.writeFile out txt
      logMsgIO opts 0 $ "Serialization successful."
      case (optCheckSerialization opts) of
        True -> checkSerialization sym opts env out
        False -> return $ Map.empty

    getFormula :: (ElemKey, IO FS.SExpr) -> IO (Either FS.SExpr FS.SExpr)
    getFormula (key, getresult) = do
      result <- getresult
      case key of
        KeyInstr _ -> return $ Left result
        KeyFun _ -> return $ Right result

checkSerialization :: (WI.IsSymExprBuilder sym, ShowF (WI.SymExpr sym))
                   => sym
                   -> TranslatorOptions
                   -> FS.NamedSymFnEnv sym
                   -> FilePath
                   -> IO (FS.NamedSymFnEnv sym)
checkSerialization sym opts env fp = do
  logMsgIO opts 0 $ "Deserializing formulas from: " ++ fp
  sexpr <- T.readFile fp >>= FS.parseSExpr
  fns <- FS.deserializeSymFnEnv sym env (FS.uninterpFunctionMaker sym) sexpr
  logMsgIO opts 0 $ "Successfully deserialized: " ++ show (length fns) ++ " formulas."
  return (Map.fromList $ fns)

translateAndSimulate' :: HasCallStack
                => TranslatorOptions
                -> ASLSpec
                -> SigEnv
                -> SigState
                -> IO (SigMap arch)
translateAndSimulate' opts spec env state = do
  let doInstrFilter (daEnc, (instr, enc)) = do
        let test = instrFilter $ optFilters $ opts
        test (instrToIdent daEnc instr enc)

  let encodings = filter doInstrFilter $ getEncodingConstraints (aslInstructions spec)
  (sigs, sigmap) <- runSigMapWithScope opts state env $ do
    forM (zip [1..] encodings) $ \(i :: Int, (daEnc, (instr, instrEnc))) -> do
      logMsgStr 1 $ "Processing instruction: " ++ DA.encName daEnc ++ " (" ++ DA.encASLIdent daEnc ++ ")"
        ++ "\n" ++ show i ++ "/" ++ show (length encodings)
      runTranslation daEnc instr instrEnc   
  IO.withFile "./output/global_sigs.txt" IO.WriteMode $ \handle -> do
    forM_ (catMaybes sigs) $ \(SomeInstructionSignature sig) -> do
      hPutStrLn handle $ T.unpack $ funcName sig
      FC.forFC_ (funcGlobalReadReprs sig) $ \(AC.LabeledValue nm ty) -> do
        hPutStrLn handle $ "  " ++ T.unpack nm ++ ": " ++ show ty
  return sigmap
      

runTranslation :: DA.Encoding
               -> AS.Instruction
               -> AS.InstructionEncoding
               -> SigMapM arch (Maybe SomeInstructionSignature)
runTranslation daEnc instr instrEnc = do
  let instrIdent = instrToIdent daEnc instr instrEnc
  logMsgStr 2 $ "Computing instruction signature for: " ++ prettyIdent instrIdent
  result <- liftSigM (KeyInstr instrIdent) $
    computeInstructionSignature daEnc instr instrEnc
  case result of
    Left err -> do
      logMsgStr (-1) $ "Error computing instruction signature: " ++ show err
      return Nothing
    Right (SomeInstructionSignature iSig, instStmts) -> do

      logMsgStr 2 $ "Translating instruction: " ++ prettyIdent instrIdent
      logMsgStr 2 $ (show iSig)
      defs <- getDefs
      minstr <- translateInstruction instrIdent iSig instStmts defs
      let deps = maybe Set.empty AC.funcDepends minstr
      MSS.gets (optTranslationDepth . sOptions) >>= \case
        TranslateRecursive -> do
          logMsg 2 $ "--------------------------------"
          logMsg 2 $ "Translating functions: "
          alldeps <- mapM (translationLoop instrIdent [] defs) (Set.toList deps)
          let alldepsSet = Set.union (Set.unions alldeps) (finalDepsOf deps)
          MSS.modify' $ \s -> s { instrDeps = Map.insert instrIdent alldepsSet (instrDeps s) }
        TranslateShallow -> return ()
      maybeSimulateInstruction instrIdent minstr
      return $ Just $ SomeInstructionSignature iSig

getDefs :: SigMapM arch (Definitions arch)
getDefs = do
  env <- MSS.gets sigEnv
  state <- MSS.gets sigState
  return $ getDefinitions env state

translationLoop :: InstructionIdent
                -> [T.Text]
                -> Definitions arch
                -> (T.Text, StaticValues)
                -> SigMapM arch (Set.Set T.Text)
translationLoop fromInstr callStack defs (fnname, env) = do
  let finalName = (mkFinalFunctionName env fnname)
  fdeps <- MSS.gets funDeps
  case Map.lookup finalName fdeps of
    Just deps -> return deps
    _ -> do
      filteredOut <- isFunFilteredOut fromInstr finalName
      if filteredOut
      then return Set.empty
      else do
        result <- liftSigM (KeyFun finalName) $ do
          case Map.lookup fnname (defSignatures defs) of
             Just (ssig, stmts) -> do
               sig <- mkSignature env ssig
               return (sig, stmts)
             Nothing -> E.throwError $ MissingSigFunctionDefinition finalName
        case result of
          Left _ -> do
            return Set.empty
          Right (Some (SomeFunctionSignature sig), stmts) -> do
            logMsgStr 2 $ "Translating function: " ++ show finalName ++ " for instruction: "
               ++ prettyIdent fromInstr
               ++ "\n CallStack: " ++ show callStack
               ++ "\n" ++ show sig ++ "\n"
            mfunc <- translateFunction finalName sig stmts defs
            let deps = maybe Set.empty AC.funcDepends mfunc
            logMsgStr 2 $ "Function Dependencies: " ++ show deps
            MSS.modify' $ \s -> s { funDeps = Map.insert finalName Set.empty (funDeps s) }
            alldeps <- mapM (translationLoop fromInstr (finalName : callStack) defs) (Set.toList deps)
            let alldepsSet = Set.union (Set.unions alldeps) (finalDepsOf deps)
            MSS.modify' $ \s -> s { funDeps = Map.insert finalName alldepsSet (funDeps s) }
            maybeSimulateFunction fromInstr finalName mfunc
            return alldepsSet

runSigMapWithScope :: TranslatorOptions
                    -> SigState
                    -> SigEnv
                    -> SigMapM arch a
                    -> IO (a, SigMap arch)
runSigMapWithScope opts sigState sigEnv action = do
  handleAllocator <- CFH.newHandleAllocator
  let sigMap =
        SigMap {
            instrExcepts = Map.empty
          , funExcepts = Map.empty
          , sigState = sigState
          , sigEnv = sigEnv
          , instrDeps = Map.empty
          , funDeps = Map.empty
          , sOptions = opts
          , sHandleAllocator = handleAllocator
          , sFormulaPromises = []
          }
  runSigMapM action sigMap

withOnlineBackend' :: forall a
                    . (forall scope. CBO.YicesOnlineBackend scope (B.Flags B.FloatReal) -> IO a)
                   -> IO a
withOnlineBackend' action = do
  let feat =     useIntegerArithmetic
             .|. useBitvectors
             .|. useStructs
  Some gen <- newIONonceGenerator
  CBO.withOnlineBackend B.FloatRealRepr gen feat $ \sym -> do
    WC.extendConfig Yices.yicesOptions (WI.getConfiguration sym)
    action sym

withOnlineBackend :: forall arch a
                   . ElemKey
                  -> (forall scope. CBO.YicesOnlineBackend scope (B.Flags B.FloatReal) -> IO a)
                  -> SigMapM arch (Maybe a)
withOnlineBackend key action = catchIO key $ withOnlineBackend' action

-- Extremely vague measure of function body size
measureStmts :: [AS.Stmt] -> Int
measureStmts stmts = getSum $ runIdentity $ mconcat <$> traverse (TR.collectSyntax doCollect) stmts
  where
    doCollect :: TR.KnownSyntaxRepr t => t -> Identity (Sum Int)
    doCollect _ = return 1

-- | Translate an ASL instruction or function into a crucible CFG.
-- Optionally we may return Nothing if translation fails and we are capturing
-- the resulting exception instead of throwing it.
translateFunction :: T.Text
                  -> FunctionSignature globalReads globalWrites init tps
                  -> [AS.Stmt]
                  -> Definitions arch
                  -> SigMapM arch (Maybe (AC.Function arch globalReads globalWrites init tps))
translateFunction name sig stmts defs = do
  logMsgStr 2 $ "Rough function body size:" ++ show (measureStmts stmts)
  handleAllocator <- MSS.gets sHandleAllocator
  catchIO (KeyFun name) $ AC.functionToCrucible defs sig handleAllocator stmts

translateInstruction :: InstructionIdent
                     -> FunctionSignature globalReads globalWrites init Ctx.EmptyCtx
                     -> [AS.Stmt]
                     -> Definitions arch
                     -> SigMapM arch (Maybe (AC.Instruction arch globalReads globalWrites init))
translateInstruction ident sig stmts defs = do
  logMsgStr 2 $ "Rough instruction body size:" ++ show (measureStmts stmts)
  handleAllocator <- MSS.gets sHandleAllocator
  catchIO (KeyInstr ident) $ AC.instructionToCrucible defs sig handleAllocator stmts


-- | Simulate a function if we have one, and it is not filtered out.
-- If we are skipping translation, then simply emit an uninterpreted function with
-- the correct signature
maybeSimulateFunction :: InstructionIdent
                      -> T.Text
                      -> Maybe (AC.Function arch globalReads globalWrites init tps)
                      -> SigMapM arch ()
maybeSimulateFunction _ _ Nothing = return ()
maybeSimulateFunction fromInstr name (Just func) = do
  let key = KeyFun name
  isKeySimFilteredOut fromInstr key >>= \case
    False -> simulateGenFunction key (\cfg -> U.SomeSome <$> ASL.simulateFunction cfg func)
    True -> mkUninterpretedFun key (AC.funcSig func)

maybeSimulateInstruction :: InstructionIdent
                         -> Maybe (AC.Instruction arch globalReads globalWrites init)
                         -> SigMapM arch ()
maybeSimulateInstruction _ Nothing = return ()
maybeSimulateInstruction ident (Just instr) = do
  let key = KeyInstr ident
  isKeySimFilteredOut ident key >>= \case
    False -> simulateGenFunction key (\cfg -> U.SomeSome <$> ASL.simulateInstruction cfg instr)
    True -> mkUninterpretedFun key (AC.funcSig instr)

mkUninterpretedFun :: ElemKey -> FunctionSignature globalReads globalWrites init tps -> SigMapM arch ()
mkUninterpretedFun key sig = do
  Just (SomeSymFn symFn) <- withOnlineBackend key $ \sym -> do
     let symbol = U.makeSymbol (T.unpack (funcName sig))
     let retT = funcSigBaseRepr sig
     let argTs = funcSigAllArgsRepr sig
     SomeSymFn <$> WI.freshTotalUninterpFn sym symbol argTs retT
  addFormula key symFn

data SomeSymFn where
  SomeSymFn :: B.ExprSymFn scope args ret -> SomeSymFn

addFormula :: ElemKey -> B.ExprSymFn scope args ret -> SigMapM arch ()
addFormula key symFn = do
  let serializedSymFn = FS.serializeSymFn symFn
  let result = return serializedSymFn
  MSS.modify $ \st -> st { sFormulaPromises = (key, result) : (sFormulaPromises st) }

data SimulationException where
  SimulationDeserializationFailure :: String -> T.Text -> SimulationException
  SimulationDeserializationMismatch :: forall t args args' ret ret'
                                     . T.Text
                                    -> (B.ExprSymFn t args ret)
                                    -> (B.ExprSymFn t args' ret')
                                    -> SimulationException
  SimulationFailure :: T.Text -> SimulationException

instance Show SimulationException where
  show se = case se of
    SimulationDeserializationFailure err formula ->
      "SimulationDeserializationFailure:\n" ++ err ++ "\n" ++ T.unpack formula
    SimulationDeserializationMismatch _sexpr symFn symFn' ->
     PP.render $ PP.vcat $
      [ PP.text "SimulationDeserializationMismatch"
      , PP.text "Expected:"
      , prettySymFn symFn
      , prettySymFnBody symFn
      , PP.text "Got: "
      , prettySymFn symFn'
      , prettySymFnBody symFn'
      ]
    SimulationFailure msg -> "SimulationFailure:" ++ T.unpack msg
instance X.Exception SimulationException

prettySymFn :: B.ExprSymFn t args ret -> PP.Doc
prettySymFn symFn =
  PP.hcat $ [
      PP.text (show $ B.symFnName symFn)
    , PP.text " ("
    , PP.text (show $ WI.fnArgTypes symFn)
    , PP.text ") -> "
    , PP.text (show $ WI.fnReturnType symFn)
    ]

prettySymFnBody :: B.ExprSymFn t args ret -> PP.Doc
prettySymFnBody symFn = case B.symFnInfo symFn of
  B.DefinedFnInfo _ fnexpr _ -> showExpr fnexpr
  _ -> PP.text "[[uninterpreted]]"

showExpr :: B.Expr t ret -> PP.Doc
showExpr e = PP.text (LPP.displayS (LPP.renderPretty 0.4 80 (WI.printSymExpr e)) "")

doSimulation :: TranslatorOptions
             -> CFH.HandleAllocator
             -> T.Text
             -> (forall scope. ASL.SimulatorConfig scope -> IO (U.SomeSome (B.ExprSymFn scope)))
             -> IO FS.SExpr
doSimulation opts handleAllocator name p = do
  let
    trySimulation :: forall scope
                   . ASL.SimulatorConfig scope
                  -> IO (U.SomeSome (B.ExprSymFn scope))
    trySimulation cfg = do
      p cfg
        `X.catch`
        \(e :: X.SomeException) -> do
          X.throw $ SimulationFailure $ T.pack (show e)

    isCheck = optCheckSerialization opts
  withOnlineBackend' $ \backend -> do
    let cfg = ASL.SimulatorConfig { simOutputHandle = IO.stdout
                                  , simHandleAllocator = handleAllocator
                                  , simSym = backend
                                  }
    when isCheck $ B.startCaching backend
    logMsgIO opts 2 $ "Simulating: " ++ show name
    U.SomeSome symFn <- trySimulation cfg
    (symFnSExpr, fenv) <- return $ FS.serializeSymFn' symFn

    when isCheck $ do
      serializedSymFn <- return $ FS.printSExpr symFnSExpr
      symFnSExpr' <- FS.parseSExpr serializedSymFn
      SomeSome symFn' <- FS.deserializeSymFn backend fenv symFnSExpr'
      WN.testEquivSymFn backend symFn symFn' >>= \case
        WN.ExprUnequal ->
          X.throw $ SimulationDeserializationMismatch serializedSymFn symFn  symFn'
        _ -> logMsgIO opts 2 $ "Deserialized function matches."
    return $! FS.mkSymFnEnvEntry name symFnSExpr


-- | Simulate the given crucible CFG, and if it is a function add it to
-- the formula map.
simulateGenFunction :: ElemKey
                    -> (forall scope. ASL.SimulatorConfig scope -> IO (U.SomeSome (B.ExprSymFn scope)))
                    -> SigMapM arch ()
simulateGenFunction key p = do
  opts <- MSS.gets sOptions
  halloc <- MSS.gets sHandleAllocator

  let doSim = doSimulation opts halloc name p
  getresult <- case optParallel opts of
    True -> forkedResult doSim
    False -> (return) <$> liftIO doSim
  MSS.modify $ \st -> st { sFormulaPromises = (key, getresult) : (sFormulaPromises st) }
  where
    name = case key of
      KeyInstr ident -> T.pack $ iOpName ident
      KeyFun nm -> nm

    forkedResult :: IO FS.SExpr
                 -> SigMapM arch (IO FS.SExpr)
    forkedResult f = do
      opts <- MSS.gets sOptions
      liftIO $ do
        mvar <- newEmptyMVar
        tid <- IO.myThreadId
        void $ IO.forkFinally f $ \case
          Left ex -> do
            logMsgIO opts (-1) $ show ex
            IO.throwTo tid ex
          Right result -> putMVar mvar result
        return (takeMVar mvar)

getASL :: TranslatorOptions -> IO (ASLSpec)
getASL opts = do
  let getPath f = (fpDataRoot (optFilePaths opts)) ++ (f (optFilePaths opts))
  eAslDefs <- AP.parseAslDefsFile (getPath fpDefs)
  eAslSupportDefs <- AP.parseAslDefsFile (getPath fpSupport)
  eAslExtraDefs <- AP.parseAslDefsFile (getPath fpExtraDefs)
  eAslInsts <- AP.parseAslInstsFile (getPath fpInsts)
  eAslRegs <- AP.parseAslRegsFile (getPath fpRegs)
  case (eAslInsts, eAslDefs, eAslRegs, eAslExtraDefs, eAslSupportDefs) of
    (Left err, _, _, _, _) -> do
      hPutStrLn stderr $ "Error loading ASL instructions: " ++ show err
      exitFailure
    (_, Left err, _, _, _) -> do
      hPutStrLn stderr $ "Error loading ASL definitions: " ++ show err
      exitFailure
    (_, _, Left err ,_, _) -> do
      hPutStrLn stderr $ "Error loading ASL registers: " ++ show err
      exitFailure
    (_, _, _ , Left err, _) -> do
      hPutStrLn stderr $ "Error loading extra ASL definitions: " ++ show err
      exitFailure
    (_, _, _ , _, Left err) -> do
      hPutStrLn stderr $ "Error loading ASL support definitions: " ++ show err
      exitFailure
    (Right aslInsts, Right aslDefs, Right aslRegs, Right aslExtraDefs, Right aslSupportDefs) -> do
      return $ prepASL $ ASLSpec aslInsts aslDefs aslSupportDefs aslExtraDefs aslRegs

logMsgIO :: HasCallStack => TranslatorOptions -> Integer -> String -> IO ()
logMsgIO opts logLvl msg = do
  let logCfg = optLogCfg opts
  Log.writeLogEvent logCfg Ghc.callStack (logIntToLvl logLvl) msg

isKeySimFilteredOut :: InstructionIdent -> ElemKey -> SigMapM arch Bool
isKeySimFilteredOut fromInstr key = case key of
  KeyFun fnm -> do
    test <- MSS.gets (funSimFilter . optFilters . sOptions)
    return $ not $ test fromInstr fnm
  KeyInstr instr -> do
    test <- MSS.gets (instrSimFilter . optFilters . sOptions)
    return $ not $ test instr

isFunFilteredOut :: InstructionIdent -> T.Text -> SigMapM arch Bool
isFunFilteredOut inm fnm = do
  test <- MSS.gets (funFilter . optFilters . sOptions)
  return $ not $ test inm fnm

-- | Manually-derived list of known and expected exception categories
data ExpectedException =
  -- | See: <https://github.com/GaloisInc/asl-translator/issues/8>
    ASLSpecMissingZeroCheck
   deriving (Eq, Ord, Show)

expectedExceptions :: ElemKey -> TranslatorException -> Maybe ExpectedException
expectedExceptions k ex = case ex of
  TExcept _ (UnsupportedType (AS.TypeFun "bits" (AS.ExprLitInt 0)))
    | KeyInstr (InstructionIdent nm _ _ _) <- k
    , nm `elem` ["aarch32_USAT16_A", "aarch32_USAT_A"] ->
      Just $ ASLSpecMissingZeroCheck
  _ -> Nothing

isUnexpectedException :: ElemKey -> TranslatorException -> Bool
isUnexpectedException k e = expectedExceptions k e == Nothing

forMwithKey_ :: Applicative t => Map k a -> (k -> a -> t b) -> t ()
forMwithKey_ m f = void $ Map.traverseWithKey f m

-- | Report the results of the given translation/simulation according to
-- the given 'StatOptions'
reportStats :: StatOptions -> SigMap arch -> IO ()
reportStats sopts sm = do
  let expectedInstrs = Map.foldrWithKey (addExpected . KeyInstr) Map.empty (instrExcepts sm)
  let expected = Map.foldrWithKey (addExpected . KeyFun) expectedInstrs (funExcepts sm)
  let unexpectedElems =
        Set.union (Set.map KeyInstr $ Map.keysSet (instrExcepts sm)) (Set.map KeyFun $ Map.keysSet (funExcepts sm))
        Set.\\ (Set.unions $ Map.elems expectedInstrs ++ Map.elems expected)
  when (not (Set.null unexpectedElems)) $ do
    putStrLn $ "Unexpected exceptions:"
    forMwithKey_ (instrExcepts sm) $ \ident -> \e ->
      E.when (unexpected (KeyInstr ident) e) $ do
        putStrLn $ prettyIdent ident ++ " failed to translate:"
        putStrLn $ show e
    putStrLn "----------------------"
    forMwithKey_ (instrDeps sm) $ \ident -> \deps -> do
      let errs' = catMaybes $ (\dep -> (\x -> (dep,x)) <$> Map.lookup dep (funExcepts sm)) <$> (Set.toList deps)
      let errs = filter (\(dep, x) -> unexpected (KeyFun dep) x) errs'
      if null errs then return ()
      else do
        putStrLn $ prettyIdent ident ++ " has failing dependencies:"
        mapM_ (\(dep, err) -> putStrLn $ show dep <> ":" <> show err) errs
    putStrLn "----------------------"
  when (reportKnownExceptions sopts) $ do
    forMwithKey_ expected $ \ex -> \ks -> do
      putStrLn $ "Failures due to known exception: " <> show ex
      putStrLn "----------------------"
      mapM_ printKey ks
      putStrLn ""
    return ()
  putStrLn $ "Total instructions inspected: " <> show (Map.size $ instrDeps sm)
  putStrLn $ "Total functions inspected: " <> show (Map.size $ funDeps sm)
  putStrLn $ "Number of instructions which raised exceptions: " <> show (Map.size $ instrExcepts sm)
  putStrLn "----------------------"
  when (reportSucceedingInstructions sopts) $
    putStrLn $ "Instructions with no errors in any dependent functions:"
  r <- Map.traverseMaybeWithKey (\ident -> \deps -> do
    if not (Map.member ident (instrExcepts sm)) &&
       Set.null (Set.filter (\dep -> Map.member dep (funExcepts sm)) deps)
    then do
      E.when (reportSucceedingInstructions sopts) $ putStrLn $ prettyIdent ident
      return $ Just ident
    else return Nothing) (instrDeps sm)
  putStrLn $ "Number of successfully translated functions: " <> show (Map.size $ r)
  where
    reverseDependencyMap =
        Map.fromListWith (++) $ concat $ map (\(instr, funs) -> map (\fun -> (fun, [instr])) (Set.toList funs))
           (Map.assocs (instrDeps sm))
    printKey k = case k of
      KeyInstr ident -> putStrLn $ "Instruction: " <> prettyIdent ident
      KeyFun nm -> do
        putStrLn $ "Function: " <> show nm
        E.when (reportFunctionDependencies sopts) $ do
          putStrLn $ "Which is depended on by: "
          case Map.lookup nm reverseDependencyMap of
            Just instrs -> mapM_ (\ident -> putStrLn $  "    " <> prettyIdent ident) instrs
            _ -> return ()
    unexpected k err =
      if reportAllExceptions sopts then True else isUnexpectedException k err
    addExpected nm err = case expectedExceptions nm err of
      Just e -> if (reportKnownExceptionFilter sopts e)
                then Map.insertWith Set.union e (Set.singleton nm)
                else id
      Nothing -> id

prettyIdent :: InstructionIdent -> String
prettyIdent (InstructionIdent _ _ _ opnm) = opnm


prettyKey :: ElemKey -> String
prettyKey (KeyInstr ident) = prettyIdent ident
prettyKey (KeyFun fnName) = T.unpack fnName

data TranslatorException =
    TExcept ElemKey TranslationException
  | SExcept ElemKey SigException
  | SimExcept ElemKey SimulationException
  | BadTranslatedInstructionsFile
  | SomeExcept X.SomeException

instance Show TranslatorException where
  show e = case e of
    TExcept k te -> "Translator exception in: " ++ prettyKey k ++ "\n" ++ prettyTExcept te
    SExcept k se -> "Signature exception in:" ++ prettyKey k ++ "\n" ++ show se
    SimExcept k se -> "Simulation exception in:" ++ prettyKey k ++ "\n" ++ show se
    SomeExcept err -> "General exception:\n" ++ show err
    BadTranslatedInstructionsFile -> "Failed to load translated instructions."

prettyTExcept :: TranslationException -> String
prettyTExcept te = case te of
  GlobalsError msg -> "GlobalsError: \n" ++ msg
  _ -> show te

instance X.Exception TranslatorException

data InstructionIdent =
  InstructionIdent { iName :: T.Text, iEnc :: T.Text, iSet :: AS.InstructionSet, iOpName :: String }
  deriving (Eq, Ord, Show)

instrToIdent :: DA.Encoding -> AS.Instruction -> AS.InstructionEncoding -> InstructionIdent
instrToIdent daEnc instr enc =
  InstructionIdent (AS.instName instr) (AS.encName enc) (AS.encInstrSet enc) (DA.encName daEnc)

finalDepsOf :: Set.Set (T.Text, StaticValues) -> Set.Set T.Text
finalDepsOf deps = Set.map (\(nm, env) -> mkFinalFunctionName env nm) deps

data Filters = Filters { funFilter :: InstructionIdent -> T.Text -> Bool
                       , instrFilter :: InstructionIdent -> Bool
                       , funSimFilter :: InstructionIdent -> T.Text -> Bool
                       , instrSimFilter :: InstructionIdent -> Bool
                       }

data ElemKey =
   KeyInstr InstructionIdent
 | KeyFun T.Text
 deriving (Eq, Ord, Show)


-- | The internal state of the Driver, collecting any raised exceptions during
-- translation/simulation as well as the final serialized What4 function for each
-- ASL function and instruction.
data SigMap arch where
  SigMap :: { instrExcepts :: Map.Map InstructionIdent TranslatorException
            , funExcepts :: Map.Map T.Text TranslatorException
            , sigState :: SigState
            , sigEnv :: SigEnv
            , instrDeps :: Map.Map InstructionIdent (Set.Set T.Text)
            , funDeps :: Map.Map T.Text (Set.Set T.Text)
            , sOptions :: TranslatorOptions
            , sHandleAllocator :: CFH.HandleAllocator
            , sFormulaPromises :: [(ElemKey, IO FS.SExpr)]
            } -> SigMap arch

getInstructionMap :: [AS.Instruction] -> Map.Map String (AS.Instruction, AS.InstructionEncoding)
getInstructionMap instrs = Map.fromList $ concat $
  map (\instr -> [ (encodingIdentifier instr enc, (instr, enc)) | enc <- AS.instEncodings instr ] ) instrs

getEncodingConstraints :: [AS.Instruction] -> [(DA.Encoding, (AS.Instruction, AS.InstructionEncoding))]
getEncodingConstraints instrs =
  map getEnc (Map.elems A32.aslEncodingMap)
  ++ map getEnc (Map.elems T32.aslEncodingMap)
  where
    instructionMap = getInstructionMap instrs

    getEnc :: DA.Encoding -> (DA.Encoding, (AS.Instruction, AS.InstructionEncoding))
    getEnc enc = case Map.lookup (DA.encASLIdent enc) instructionMap of
      Just instr -> (enc, instr)
      Nothing -> error $ "Missing encoding for: " ++ show (DA.encASLIdent enc)

newtype SigMapM arch a = SigMapM (MSS.StateT (SigMap arch) IO a)
  deriving ( Functor
           , Applicative
           , Monad
           , MSS.MonadState (SigMap arch)
           , MonadIO
           , MF.MonadFail
           )

instance MonadLog (SigMapM arch) where
  logMsg logLvl msg = do
    logCfg <- MSS.gets (optLogCfg . sOptions)
    liftIO $ Log.logIOWith logCfg (logIntToLvl logLvl) (T.unpack msg)

runSigMapM :: SigMapM arch a -> SigMap arch -> IO (a, SigMap arch)
runSigMapM (SigMapM m) = MSS.runStateT m

liftSigM :: ElemKey -> SigM ext f a -> SigMapM arch (Either SigException a)
liftSigM k f = do
  state <- MSS.gets sigState
  env <- MSS.gets sigEnv
  logCfg <- MSS.gets (optLogCfg . sOptions)
  (result, state') <- liftIO $ runSigM f env state logCfg
  case result of
    Right a -> do
      MSS.modify' $ \s -> s { sigState = state' }
      return $ Right a
    Left err -> do
      collectExcept k (SExcept k err)
      return $ Left err

getExceptionFilter :: SigMapM arch (ElemKey -> TranslatorException -> Bool)
getExceptionFilter = do
  collectAllExceptions <- MSS.gets (optCollectAllExceptions . sOptions)
  collectExpectedExceptions <- MSS.gets (optCollectExpectedExceptions . sOptions)
  return $ \k e ->
    (collectAllExceptions || ((not $ isUnexpectedException k e) && collectExpectedExceptions))

collectExcept :: ElemKey -> TranslatorException -> SigMapM arch ()
collectExcept k e = do
  f <- getExceptionFilter
  if f k e then case k of
    KeyInstr ident -> MSS.modify' $ \s -> s { instrExcepts = Map.insert ident e (instrExcepts s) }
    KeyFun fun -> MSS.modify' $ \s -> s { funExcepts = Map.insert fun e (funExcepts s) }
  else X.throw e

catchIO :: ElemKey -> (HasLogCfg => IO a) -> SigMapM arch (Maybe a)
catchIO k f = do
  logCfg <- MSS.gets (optLogCfg . sOptions)
  withLogCfg logCfg $ do
    a <- liftIO ((Left <$> f)
                    `X.catch` (\(e :: TranslationException) -> return $ Right $ TExcept k e)
                    `X.catch` (\(e :: SimulationException) -> return $ Right $ SimExcept k e)
                    `X.catch` (\(e :: X.SomeException) -> return $ Right (SomeExcept e)))
    case a of
      Left r -> return (Just r)
      Right err -> (\_ -> Nothing) <$> collectExcept k err

optFilters :: TranslatorOptions -> Filters
optFilters opts =
  addTranslationFilter (optTranslationMode opts)  $
  addSimulationFilter (optSimulationMode opts) noFilter

addTranslationFilter :: TranslationMode -> (Filters -> Filters)
addTranslationFilter tmode = case tmode of
  TranslateAArch32 -> translateArch32
  TranslateInstruction (instr, enc) -> translateOnlyInstr (instr, enc)

addSimulationFilter :: SimulationMode -> (Filters -> Filters)
addSimulationFilter smode = case smode of
  SimulateAll -> simulateAll
  SimulateFunctions -> simulateFunctionsFilter
  SimulateInstructions -> simulateInstructionsFilter
  SimulateInstruction (instr, enc) -> simulateOnlyInstr  (instr, enc)
  SimulateNone -> simulateNone



noFilter :: Filters
noFilter = Filters
  (\_ -> \_ -> True)
  (\_ -> True)
  (\_ -> \_ -> True)
  (\_ -> True)

translateOnlyInstr :: (T.Text, T.Text) -> Filters -> Filters
translateOnlyInstr inm f =
  f { funFilter = (\(InstructionIdent nm enc _ _) -> \_ -> inm == (nm, enc))
    , instrFilter = (\(InstructionIdent nm enc _ _) -> (nm, enc) == inm)
    }

translateArch32 :: Filters -> Filters
translateArch32 f =
  f { funFilter = (\(InstructionIdent _ _ iset _) -> \_ -> iset `elem` [AS.A32, AS.T32, AS.T16] )
    , instrFilter = (\(InstructionIdent _ _ iset _) -> iset `elem` [AS.A32, AS.T32, AS.T16])
    }

simulateAll :: Filters -> Filters
simulateAll f =
  f { funSimFilter = \_ _ -> True
    , instrSimFilter = \_ -> True
    }

simulateInstructionsFilter :: Filters -> Filters
simulateInstructionsFilter f =
  f { funSimFilter = \_ _ -> False
    , instrSimFilter = \_ -> True
    }

simulateFunctionsFilter :: Filters -> Filters
simulateFunctionsFilter f =
  f { funSimFilter = \_ _ -> True
    , instrSimFilter = \_ -> False
    }

simulateOnlyInstr :: (T.Text, T.Text) -> Filters -> Filters
simulateOnlyInstr inm f =
  f { funSimFilter = (\(InstructionIdent nm enc _ _) -> \_ -> inm == (nm, enc))
    , instrSimFilter = (\(InstructionIdent nm enc _ _) -> (nm, enc) == inm)
    }


simulateNone :: Filters -> Filters
simulateNone f =
  f { funSimFilter = \_ _ -> False
    , instrSimFilter = \_ -> False
    }
