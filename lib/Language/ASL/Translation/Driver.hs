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
  , StatOptions(..)
  , TranslationDepth(..)
  , FilePathConfig(..)
  , runWithFilters
  , reportStats
  , serializeFormulas
  , getTranslationMode
  , getSimulationMode
  , noFilter
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

import           Data.Map ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Maybe ( catMaybes, mapMaybe )
import           Data.Monoid
import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import           Data.Bits( (.|.) )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import qualified Data.Text.IO as T

import qualified Data.List as List
import qualified Data.List.Split as List
import           Data.List.Index (imap)
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
import           Panic hiding (panic)
import           Lang.Crucible.Panic ( Crucible )

import qualified Language.ASL.SyntaxTraverse as AS  ( pattern VarName )
import qualified Language.ASL.SyntaxTraverse as TR

import qualified Language.ASL as ASL

import qualified Language.ASL.Crucible as AC

import           Language.ASL.Translation
import           Language.ASL.Translation.Preprocess
import           Language.ASL.Translation.Exceptions
import           Language.ASL.Signature
import           Language.ASL.StaticExpr

import qualified What4.Expr.Builder as B
import qualified What4.Interface as WI
import qualified What4.Solver.Yices as Yices
import qualified What4.Config as WC
import           What4.ProblemFeatures

import qualified What4.Serialize.Printer as WP
import qualified What4.Serialize.Parser as WP
import qualified What4.Serialize.Normalize as WN

import qualified Text.PrettyPrint.HughesPJClass as PP
import qualified Text.PrettyPrint.ANSI.Leijen as LPP

-- FIXME: this should be moved somewhere general
import           What4.Utils.Log ( HasLogCfg, LogLevel(..), LogCfg, withLogCfg )
import qualified What4.Utils.Log as Log
import qualified What4.Utils.Util as U
import           Util.Log ( MonadLog(..), logIntToLvl, logMsgStr )

data TranslatorOptions = TranslatorOptions
  { optVerbosity :: Integer
  , optNumberOfInstructions :: Maybe Int
  , optFilters :: Filters
  , optCollectAllExceptions :: Bool
  , optCollectExpectedExceptions :: Bool
  , optTranslationDepth :: TranslationDepth
  , optCheckSerialization :: Bool
  , optFilePaths :: FilePathConfig
  , optLogCfg :: LogCfg
  , optParallel :: Bool
  }

data FilePathConfig = FilePathConfig
  { fpDefs :: FilePath
  , fpInsts :: FilePath
  , fpRegs :: FilePath
  , fpSupport :: FilePath
  , fpExtraDefs :: FilePath
  , fpOutput :: FilePath
  , fpDataRoot :: FilePath
  }

data StatOptions = StatOptions
  { reportKnownExceptions :: Bool
  , reportSucceedingInstructions :: Bool
  , reportAllExceptions :: Bool
  , reportKnownExceptionFilter :: ExpectedException -> Bool
  , reportFunctionDependencies :: Bool
  }

data TranslationDepth = TranslateRecursive
                      | TranslateShallow

runWithFilters :: HasCallStack => TranslatorOptions -> IO (SigMap arch)
runWithFilters opts = do
  spec <- getASL opts
  logMsgIO opts 0 $ "Loaded "
    ++ show (length $ aslInstructions spec) ++ " instructions and "
    ++ show (length $ aslDefinitions spec) ++ " definitions and "
    ++ show (length $ aslSupportDefinitions spec) ++ " support definitions and "
    ++ show (length $ aslExtraDefinitions spec) ++ " extra definitions and "
    ++ show (length $ aslRegisterDefinitions spec) ++ " register definitions."
  (sigEnv, sigState) <- buildSigState spec (optLogCfg opts)
  runWithFilters' opts spec sigEnv sigState

data BuilderData t = NoBuilderData

optFormulaOutputFilePath :: TranslatorOptions -> FilePath
optFormulaOutputFilePath opts = fpOutput (optFilePaths opts)


-- FIXME: manually shaping an s-expression to fit the form that
-- the current what4 deserializer is expecting. This needs to be done
-- correctly once the new printer/parser is in place.
serializeFormulas :: TranslatorOptions -> SigMap arch -> IO ()
serializeFormulas opts (sFormulaPromises -> promises) = do
  formulas <- mapM getFormula promises
  let out = optFormulaOutputFilePath opts
  logMsgIO opts 0 $ "Writing formulas to: " ++  out
  T.writeFile out (T.unlines $ (["(symfnenv ("] ++ reverse formulas ++ ["))"]))
  logMsgIO opts 0 $ "Serialization successful."
  when (optCheckSerialization opts) $ checkSerialization opts
  where
    getFormula :: (T.Text, IO (Either SimulationException T.Text)) -> IO T.Text
    getFormula (name, getresult) = getresult >>= \case
      Left err -> X.throw err
      Right result -> return $ T.concat ["(\"", name, "\" ", result, ")"]

checkSerialization :: TranslatorOptions -> IO ()
checkSerialization opts = do
  let out = optFormulaOutputFilePath opts
  logMsgIO opts 0 $ "Deserializing formulas from: " ++ out
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr NoBuilderData r
  let logCfg = optLogCfg opts
  Log.withLogCfg logCfg $
    WP.readSymFnEnvFromFile (WP.defaultParserConfig sym) (optFormulaOutputFilePath opts) >>= \case
      Left err -> X.throw $ SimulationDeserializationFailure err ""
      Right _ -> do
        logMsgIO opts 0 $ "Deserializing successful."
        return ()

runWithFilters' :: HasCallStack
                => TranslatorOptions
                -> ASLSpec
                -> SigEnv
                -> SigState
                -> IO (SigMap arch)
runWithFilters' opts spec sigEnv sigState = do
  let numInstrs = optNumberOfInstructions opts
  let doInstrFilter (daEnc, (instr, enc)) = do
        let test = instrFilter $ optFilters $ opts
        test (instrToIdent daEnc instr enc)

  let encodings = filter doInstrFilter $ getEncodingConstraints (aslInstructions spec)
  execSigMapWithScope opts sigState sigEnv $ do
    addMemoryUFs
    forM_ (zip [1..] encodings) $ \(i :: Int, (daEnc, (instr, instrEnc))) -> do
      logMsgStr 1 $ "Processing instruction: " ++ DA.encName daEnc ++ " (" ++ DA.encASLIdent daEnc ++ ")"
        ++ "\n" ++ show i ++ "/" ++ show (length encodings)
      runTranslation daEnc instr instrEnc

runTranslation :: DA.Encoding
               -> AS.Instruction
               -> AS.InstructionEncoding
               -> SigMapM arch ()
runTranslation daEnc instr instrEnc = do
  let instrIdent = instrToIdent daEnc instr instrEnc
  logMsgStr 2 $ "Computing instruction signature for: " ++ prettyIdent instrIdent
  result <- liftSigM (KeyInstr instrIdent) $
    computeInstructionSignature daEnc instr instrEnc
  case result of
    Left err -> do
      logMsgStr (-1) $ "Error computing instruction signature: " ++ show err
    Right (Some (SomeFunctionSignature iSig), instStmts) -> do
      liftSigM (KeyInstr instrIdent) getDefinitions >>= \case
        Left err -> do
          logMsgStr (-1) $ "Error computing ASL definitions: " ++ show err
        Right defs -> do
          logMsgStr 2 $ "Translating instruction: " ++ prettyIdent instrIdent
          logMsgStr 2 $ (show iSig)
          mfunc <- translateFunction (KeyInstr instrIdent) iSig instStmts defs
          let deps = maybe Set.empty AC.funcDepends mfunc
          MSS.gets (optTranslationDepth . sOptions) >>= \case
            TranslateRecursive -> do
              logMsg 2 $ "--------------------------------"
              logMsg 2 $ "Translating functions: "
              alldeps <- mapM (translationLoop instrIdent [] defs) (Set.toList deps)
              let alldepsSet = Set.union (Set.unions alldeps) (finalDepsOf deps)
              MSS.modify' $ \s -> s { instrDeps = Map.insert instrIdent alldepsSet (instrDeps s) }
            TranslateShallow -> return ()
          maybeSimulateFunction instrIdent (KeyInstr instrIdent) mfunc

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
          Right (Some ssig@(SomeFunctionSignature sig), stmts) -> do
            MSS.modify' $ \s -> s { sMap = Map.insert finalName (Some ssig) (sMap s) }
            logMsgStr 2 $ "Translating function: " ++ show finalName ++ " for instruction: "
               ++ prettyIdent fromInstr
               ++ "\n CallStack: " ++ show callStack
               ++ "\n" ++ show sig ++ "\n"
            mfunc <- translateFunction (KeyFun finalName) sig stmts defs
            let deps = maybe Set.empty AC.funcDepends mfunc
            logMsgStr 2 $ "Function Dependencies: " ++ show deps
            MSS.modify' $ \s -> s { funDeps = Map.insert finalName Set.empty (funDeps s) }
            alldeps <- mapM (translationLoop fromInstr (finalName : callStack) defs) (Set.toList deps)
            let alldepsSet = Set.union (Set.unions alldeps) (finalDepsOf deps)
            MSS.modify' $ \s -> s { funDeps = Map.insert finalName alldepsSet (funDeps s) }
            maybeSimulateFunction fromInstr (KeyFun finalName) mfunc
            return alldepsSet

execSigMapWithScope :: TranslatorOptions
                    -> SigState
                    -> SigEnv
                    -> SigMapM arch ()
                    -> IO (SigMap arch)
execSigMapWithScope opts sigState sigEnv action = do
  handleAllocator <- CFH.newHandleAllocator
  let sigMap =
        SigMap {
          sMap = Map.empty
          , instrExcepts = Map.empty
          , funExcepts = Map.empty
          , sigState = sigState
          , sigEnv = sigEnv
          , instrDeps = Map.empty
          , funDeps = Map.empty
          , sOptions = opts
          , sHandleAllocator = handleAllocator
          , sFormulaPromises = []
          }
  execSigMapM action sigMap

withOnlineBackend' :: forall arch a
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

memoryUFSigs :: [(T.Text, ((Some (Ctx.Assignment WI.BaseTypeRepr), Some WI.BaseTypeRepr)))]
memoryUFSigs = concatMap mkUF [1,2,4,8,16]
  where
    ramRepr = WI.BaseArrayRepr (Ctx.empty Ctx.:> WI.BaseBVRepr (WI.knownNat @32)) (WI.BaseBVRepr (WI.knownNat @8))
    mkUF :: Integer -> [(T.Text, (Some (Ctx.Assignment WI.BaseTypeRepr), Some WI.BaseTypeRepr))]
    mkUF sz
      | Just (Some szRepr) <- WI.someNat sz
      , Just WI.LeqProof <- WI.knownNat @1 `WI.testLeq` szRepr
      , bvSize <- (WI.knownNat @8) `WI.natMultiply` szRepr
      , WI.LeqProof <- WI.leqMulPos (WI.knownNat @8) szRepr =
        [( "write_mem_" <> (T.pack (show sz))
         , ( Some (Ctx.empty Ctx.:> ramRepr Ctx.:> (WI.BaseBVRepr (WI.knownNat @32)) Ctx.:> WI.BaseBVRepr bvSize)
           , Some ramRepr))
        ,( "read_mem_" <> (T.pack (show sz))
         , ( Some (Ctx.empty Ctx.:> ramRepr Ctx.:> (WI.BaseBVRepr (WI.knownNat @32)))
           , Some (WI.BaseBVRepr bvSize)))
        ]
    mkUF _ = error "unreachable"

addMemoryUFs :: SigMapM arch ()
addMemoryUFs = do
  Just ufs <- withOnlineBackend (KeyFun "memory") $ \sym -> do
    forM memoryUFSigs $ \(name, (Some argTs, Some retT)) -> do
      let symbol = U.makeSymbol (T.unpack name)
      symFn <- WI.freshTotalUninterpFn sym symbol argTs retT
      return $ (name, SomeSymFn symFn)
  mapM_ (\(name, SomeSymFn symFn) -> addFormula name symFn) ufs

-- Extremely vague measure of function body size
measureStmts :: [AS.Stmt] -> Int
measureStmts stmts = getSum $ runIdentity $ mconcat <$> traverse (TR.collectSyntax doCollect) stmts
  where
    doCollect :: TR.KnownSyntaxRepr t => t -> Identity (Sum Int)
    doCollect _ = return 1

-- | Translate an ASL instruction or function into a crucible CFG.
-- Optionally we may return Nothing if translation fails and we are capturing
-- the resulting exception instead of throwing it.
translateFunction :: ElemKey
                  -> FunctionSignature globalReads globalWrites init tps
                  -> [AS.Stmt]
                  -> Definitions arch
                  -> SigMapM arch (Maybe (AC.Function arch globalReads globalWrites init tps))
translateFunction key sig stmts defs = do
  logMsgStr 2 $ "Rough function body size:" ++ show (measureStmts stmts)
  handleAllocator <- MSS.gets sHandleAllocator
  logLvl <- MSS.gets (optVerbosity . sOptions)
  catchIO key $ AC.functionToCrucible defs sig handleAllocator stmts logLvl


-- | Simulate a function if we have one, and it is not filtered out.
-- If we are skipping translation, then simply emit an uninterpreted function with
-- the correct signature
maybeSimulateFunction :: InstructionIdent
                      -> ElemKey
                      -> Maybe (AC.Function arch globalReads globalWrites init tps)
                      -> SigMapM arch ()
maybeSimulateFunction _ _ Nothing = return ()
maybeSimulateFunction fromInstr key (Just func) =
 isKeySimFilteredOut fromInstr key >>= \case
   False -> simulateFunction key func
   True -> do
     Just (SomeSymFn symFn) <- withOnlineBackend key $ \sym -> do
        let sig = AC.funcSig func
        let symbol = U.makeSymbol (T.unpack (funcName sig))
        let retT = funcSigBaseRepr sig
        let argTs = funcSigAllArgsRepr sig
        SomeSymFn <$> WI.freshTotalUninterpFn sym symbol argTs retT
     addFormula (T.pack $ prettyKey key) symFn

data SomeSymFn where
  SomeSymFn :: B.ExprSymFn scope args ret -> SomeSymFn

addFormula :: T.Text -> B.ExprSymFn scope args ret -> SigMapM arch ()
addFormula name' symFn = do
  let name = "uf." <> name'
  let (serializedSymFn, _) = WP.printSymFn' symFn
  let result = return (Right serializedSymFn)
  MSS.modify $ \st -> st { sFormulaPromises = (name, result) : (sFormulaPromises st) }

data SimulationException where
  SimulationDeserializationFailure :: String -> T.Text -> SimulationException
  SimulationDeserializationMismatch :: forall t ret ret'
                                     . T.Text
                                    -> (B.Expr t ret)
                                    -> (B.Expr t ret')
                                    -> [(Some (B.Expr t), Some (B.Expr t))]
                                    -> SimulationException
  SimulationFailure :: T.Text -> SimulationException

instance Show SimulationException where
  show se = case se of
    SimulationDeserializationFailure err formula ->
      "SimulationDeserializationFailure:\n" ++ err ++ "\n" ++ T.unpack formula
    SimulationDeserializationMismatch _sexpr expr1 expr2 env ->
     PP.render $ PP.vcat $
      [ PP.text "SimulationDeserializationMismatch" ]
      ++ showExprPair (Some expr1, Some expr2)
      ++ showExprContext 3 env
    SimulationFailure msg -> "SimulationFailure:" ++ T.unpack msg
instance X.Exception SimulationException

showExprPair :: (Some (B.Expr t), Some (B.Expr t)) -> [PP.Doc]
showExprPair (Some expr1, Some expr2) =
  [PP.text "Original Expression:", showExpr expr1, PP.text "Deserialized Expression:", showExpr expr2]

showExprContext :: Int -> [(Some (B.Expr t), Some (B.Expr t))] -> [PP.Doc]
showExprContext _ [] = []
showExprContext count env = [PP.text "With context:"] ++ concat (map showExprPair (take count env))

showExpr :: B.Expr t ret -> PP.Doc
showExpr e = PP.text (LPP.displayS (LPP.renderPretty 0.4 80 (WI.printSymExpr e)) "")


mkParserConfig :: forall sym scope
                . sym ~ CBO.YicesOnlineBackend scope (B.Flags B.FloatReal)
               => sym
               -> WP.SymFnEnv sym
               -> WP.ParserConfig sym
mkParserConfig sym fenv =
  WP.ParserConfig { pSymFnEnv = fenv
                  , pGlobalLookup = \_ -> return Nothing
                  , pOverrides = \_ -> Nothing
                  , pSym = sym
                  }

doSimulation :: forall arch globalReads globalWrites init tps
              . TranslatorOptions
             -> CFH.HandleAllocator
             -> ElemKey
             -> AC.Function arch globalReads globalWrites init tps             
             -> IO (T.Text)
doSimulation opts handleAllocator key p = do
  let
    trySimulation :: forall scope
                   . ASL.SimulatorConfig scope
                  -> IO (U.SomeSome (B.ExprSymFn scope))
    trySimulation cfg = do
      (U.SomeSome <$> ASL.simulateFunction cfg p)
        `X.catch`
        \(e :: X.SomeException) -> do
          X.throw $ SimulationFailure $ T.pack (show e)

    isCheck = optCheckSerialization opts
    logCfg = optLogCfg opts
  Some nonceGenerator <- newIONonceGenerator
  withOnlineBackend' $ \backend -> do
    let cfg = ASL.SimulatorConfig { simOutputHandle = IO.stdout
                                  , simHandleAllocator = handleAllocator
                                  , simSym = backend
                                  }
    when isCheck $ B.startCaching backend
    logMsgIO opts 2 $ "Simulating: " ++ (prettyKey key)
    U.SomeSome symFn <- trySimulation cfg
    (serializedSymFn, fenv) <- return $ WP.printSymFn' symFn
    logMsgIO opts 2 $ "Serialized formula size: " ++ show (T.length serializedSymFn)
    when isCheck $ Log.withLogCfg logCfg $ do
      WP.readSymFn (mkParserConfig backend fenv) serializedSymFn >>= \case
        Left err -> X.throw $ SimulationDeserializationFailure (show err) serializedSymFn
        Right (U.SomeSome symFn') -> do
          logMsgIO opts 2 $ "Serialization/Deserialization succeeded."
          WN.testEquivSymFn backend symFn symFn' >>= \case
            WN.ExprUnequal e1 e2 env ->
              X.throw $ SimulationDeserializationMismatch serializedSymFn e1 e2 env
            _ -> do
              logMsgIO opts 2 $ "Deserialized function matches."
    return $! serializedSymFn


-- | Simulate the given crucible CFG, and if it is a function add it to
-- the formula map.
simulateFunction :: forall arch sym globalReads globalWrites init tps
                  . ElemKey
                 -> AC.Function arch globalReads globalWrites init tps
                 -> SigMapM arch ()
simulateFunction key p = do
  opts <- MSS.gets sOptions
  halloc <- MSS.gets sHandleAllocator
 
  let name = T.pack $ "uf." ++ prettyKey key
  let doSim = doSimulation opts halloc key p
  getresult <- case optParallel opts of
    True -> forkedResult doSim
    False -> (return . Right) <$> liftIO doSim
  MSS.modify $ \st -> st { sFormulaPromises = (name, getresult) : (sFormulaPromises st) }
  where
    forkedResult :: IO T.Text
                 -> SigMapM arch (IO (Either SimulationException T.Text))
    forkedResult f = do
      opts <- MSS.gets sOptions
      exf <- getExceptionFilter
      liftIO $ do
        mvar <- newEmptyMVar
        tid <- IO.myThreadId
        void $ IO.forkFinally f $ \case
          Left ex
            | Just (e :: SimulationException) <- X.fromException ex
            , exf key (SimExcept key e) -> putMVar mvar (Left e)
          Left ex -> do
            logMsgIO opts (-1) $ show ex
            IO.throwTo tid ex
          Right result -> putMVar mvar (Right result)
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

data ExpectedException =
    RealValueUnsupported
  | InsufficientStaticTypeInformation
  | CruciblePanic
  | ASLSpecMissingZeroCheck
  | BVLengthFromGlobalState
  | PrinterParserError
   deriving (Eq, Ord, Show)

expectedExceptions :: ElemKey -> TranslatorException -> Maybe ExpectedException
expectedExceptions k ex = case ex of
  -- SimExcept _ (SimulationDeserializationMismatch _ _) -> Just $ PrinterParserError
  SExcept _ (TypeNotFound "real") -> Just $ RealValueUnsupported
  -- TExcept _ (CannotMonomorphizeFunctionCall _ _) -> Just $ InsufficientStaticTypeInformation
  -- TExcept _ (CannotStaticallyEvaluateType _ _) -> Just $ InsufficientStaticTypeInformation
  -- TExcept _ (CannotDetermineBVLength _ _) -> Just $ InsufficientStaticTypeInformation
  TExcept _ (UnsupportedType (AS.TypeFun "bits" (AS.ExprLitInt 0)))
    | KeyInstr (InstructionIdent nm _ _ _) <- k
    , nm `elem` ["aarch32_USAT16_A", "aarch32_USAT_A"] ->
      Just $ ASLSpecMissingZeroCheck
  TExcept _ (CannotStaticallyEvaluateType (AS.TypeFun "bits" (AS.ExprCall (AS.VarName fnm) _)) _)
    | fnm `elem` ["BAREGETTER_PL", "BAREGETTER_VL"] ->
      Just $ BVLengthFromGlobalState
  SomeExcept e
    | Just (Panic (_ :: Crucible) _ _ _) <- X.fromException e
    , KeyInstr (InstructionIdent nm _ _ _) <- k
    , nm `elem` ["aarch32_WFE_A", "aarch32_WFI_A", "aarch32_VTBL_A", "aarch32_VTST_A"] ->
      Just $ CruciblePanic
  SomeExcept e
    | Just (Panic (_ :: Crucible) _ _ _) <- X.fromException e
    , KeyFun nm <- k
    , nm `elem` ["AArch32_ExclusiveMonitorsPass_2"] ->
      Just $ CruciblePanic
  SomeExcept e
    | Just (ASL.SimulationAbort _ _) <- X.fromException e
    , KeyInstr (InstructionIdent nm _ _ _) <- k
    , nm `elem` [ "aarch32_VTBL_A" ] ->
      Just $ CruciblePanic
  _ -> Nothing

isUnexpectedException :: ElemKey -> TranslatorException -> Bool
isUnexpectedException k e = expectedExceptions k e == Nothing

forMwithKey_ :: Applicative t => Map k a -> (k -> a -> t b) -> t ()
forMwithKey_ m f = void $ Map.traverseWithKey f m

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
    TExcept k te -> "Translator exception in: " ++ prettyKey k ++ "\n" ++ show te
    SExcept k se -> "Signature exception in:" ++ prettyKey k ++ "\n" ++ show se
    SimExcept k se -> "Simulation exception in:" ++ prettyKey k ++ "\n" ++ show se
    SomeExcept err -> "General exception:\n" ++ show err
    BadTranslatedInstructionsFile -> "Failed to load translated instructions."

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


-- FIXME: Seperate this into RWS
data SigMap arch where
  SigMap :: { sMap :: Map.Map T.Text (Some (SomeFunctionSignature))
            , instrExcepts :: Map.Map InstructionIdent TranslatorException
            , funExcepts :: Map.Map T.Text TranslatorException
            , sigState :: SigState
            , sigEnv :: SigEnv
            , instrDeps :: Map.Map InstructionIdent (Set.Set T.Text)
            , funDeps :: Map.Map T.Text (Set.Set T.Text)
            , sOptions :: TranslatorOptions
            , sHandleAllocator :: CFH.HandleAllocator
            , sFormulaPromises :: [(T.Text, IO (Either SimulationException T.Text))]
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

execSigMapM :: SigMapM arch a -> SigMap arch -> IO (SigMap arch)
execSigMapM (SigMapM m) = MSS.execStateT m

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

getTranslationMode :: String -> Maybe (Filters -> Filters)
getTranslationMode mode = case mode of
  "all" -> return $ translateAll
  "noArch64" -> return $ translateNoArch64
  "Arch32" -> return $ translateArch32
  _ -> case List.splitOn "/" mode of
    [instr, enc] -> return $ translateOnlyInstr (T.pack instr, T.pack enc)
    _ -> fail ""

getSimulationMode :: String -> Maybe (Filters -> Filters)
getSimulationMode mode = case mode of
  "all" -> return $ simulateAll
  "instructions" -> return $ simulateInstructions
  "none" -> return $ simulateNone
  _ -> case List.splitOn "/" mode of
    [instr, enc] -> return $ simulateOnlyInstr (T.pack instr, T.pack enc)
    _ -> fail ""

noFilter :: Filters
noFilter = Filters
  (\_ -> \_ -> True)
  (\_ -> True)
  (\_ -> \_ -> True)
  (\_ -> True)

translateAll :: Filters -> Filters
translateAll f =
  f { funFilter = (\_ -> \_ -> True)
    , instrFilter = (\_ -> True)
    }

translateOnlyInstr :: (T.Text, T.Text) -> Filters -> Filters
translateOnlyInstr inm f =
  f { funFilter = (\(InstructionIdent nm enc _ _) -> \_ -> inm == (nm, enc))
    , instrFilter = (\(InstructionIdent nm enc _ _) -> (nm, enc) == inm)
    }


translateNoArch64 :: Filters -> Filters
translateNoArch64 f =
  f { funFilter = (\(InstructionIdent _ _ iset _) -> \_ -> iset /= AS.A64 )
    , instrFilter = (\(InstructionIdent _ _ iset _) -> iset /= AS.A64)
    }


translateArch32 :: Filters -> Filters
translateArch32 f =
  f { funFilter = (\(InstructionIdent _ _ iset _) -> \_ -> iset `elem` [AS.A32, AS.T32] )
    , instrFilter = (\(InstructionIdent _ _ iset _) -> iset `elem` [AS.A32, AS.T32])
    }

simulateAll :: Filters -> Filters
simulateAll f =
  f { funSimFilter = \_ _ -> True
    , instrSimFilter = \_ -> True
    }

simulateInstructions :: Filters -> Filters
simulateInstructions f =
  f { funSimFilter = \_ _ -> False
    , instrSimFilter = \_ -> True
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
