{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import           Control.Monad ( when, void )
import qualified Control.Concurrent as IO
import qualified Control.Exception as X
import           GHC.Stack ( HasCallStack )

import           Data.Maybe ( fromJust )

import           System.Exit (exitFailure)
import qualified System.Environment as IO
import qualified System.IO as IO
import           System.Console.GetOpt

import           Language.ASL.Translation.Driver ( TranslatorOptions(..), StatOptions(..)
                                                 , FilePathConfig(..), TranslationDepth(..)
                                                 )
import qualified Language.ASL.Translation.Driver as ASL

import qualified What4.Utils.Log as Log

import Debug.Trace

main :: HasCallStack => IO ()
main = do
  logCfg <- Log.mkLogCfg "main"
  stringArgs <- IO.getArgs
  let (args, rest, errs) = getOpt Permute arguments stringArgs

  when (not $ null $ errs <> rest) $ do
    usage
    exitFailure

  case foldl applyOption (Just (defaultOptions logCfg, defaultStatOptions)) args of
    Nothing -> do
      usage
      exitFailure
    Just (opts, statOpts) -> do
      mkLogEventConsumer opts
      (do 
        ASL.SomeSigMap sm <- ASL.runWithFilters opts
        ASL.reportStats statOpts sm
        ASL.serializeFormulas opts sm)
        `X.catch` \(e :: X.SomeException) -> do
                      Log.logIOWith logCfg Log.Error (show e)
                      Log.logEndWith logCfg
                      exitFailure
      Log.logEndWith logCfg
  where
    applyOption (Just (opts, statOpts)) arg = case arg of
      Left f -> do
        opts' <- f opts
        return $ (opts', statOpts)
      Right f -> do
        statOpts' <- f statOpts
        return $ (opts, statOpts')
    applyOption Nothing _ = Nothing

mkLogEventConsumer :: TranslatorOptions -> IO ()
mkLogEventConsumer opts = void $ IO.forkIO $
  (Log.consumeUntilEnd (intToLogLvlFilter (optVerbosity opts)) $ \e -> do
    if optVerbosity opts > 1 then
      traceIO (Log.prettyLogEvent e)
    else
      traceIO (simpleLogEvent e)
    IO.hFlush IO.stderr) (optLogCfg opts)
  where
    simpleLogEvent :: Log.LogEvent -> String
    simpleLogEvent le = Log.leMsg le

    intToLogLvlFilter :: Integer -> (Log.LogEvent -> Bool)
    intToLogLvlFilter i logEvent = case Log.leLevel logEvent of
      Log.Info -> i >= 1
      Log.Warn -> i >= 1
      Log.Debug -> i >= 2
      Log.Error -> True

usage :: IO ()
usage = do
  pn <- IO.getProgName
  let msg = "Usage: " <> pn <> " [options]"
  putStrLn $ usageInfo msg arguments


defaultFilePaths :: FilePathConfig
defaultFilePaths = FilePathConfig
  { fpDataRoot = "./data/Parsed/"
  , fpDefs = "arm_defs.sexpr"
  , fpInsts = "arm_instrs.sexpr"
  , fpRegs = "arm_regs.sexpr"
  , fpSupport = "support.sexpr"
  , fpExtraDefs = "extra_defs.sexpr"
  , fpOutput = "./output/formulas.what4"
  }

defaultOptions :: Log.LogCfg -> TranslatorOptions
defaultOptions logCfg = TranslatorOptions
  { optVerbosity = 1
  , optNumberOfInstructions = Nothing
  , optFilters = (fromJust $ ASL.getTranslationMode "Arch32") ASL.noFilter
  , optCollectAllExceptions = False
  , optCollectExpectedExceptions = True
  , optTranslationDepth = TranslateRecursive
  , optCheckSerialization = False
  , optFilePaths = defaultFilePaths
  , optLogCfg = logCfg
  }
  

defaultStatOptions :: StatOptions
defaultStatOptions = StatOptions
  { reportKnownExceptions = False
  , reportSucceedingInstructions = False
  , reportAllExceptions = False
  , reportKnownExceptionFilter = (\_ -> True)
  , reportFunctionDependencies = False
  }

arguments :: [OptDescr (Either (TranslatorOptions -> Maybe TranslatorOptions) (StatOptions -> Maybe StatOptions))]
arguments =
  [ Option "a" ["asl-spec"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpDataRoot = f }})) "PATH")
    ("Path to parsed ASL specification.")

  , Option "c" ["collect-exceptions"] (NoArg (Left (\opts -> Just $ opts { optCollectAllExceptions = True })))
    "Handle and collect all exceptions thrown during translation"

  , Option [] ["collect-expected-exceptions"] (NoArg (Left (\opts -> Just $ opts { optCollectExpectedExceptions = True })))
    "Handle and collect exceptions for known issues thrown during translation"

  , Option "v" ["verbosity"] (ReqArg (\f -> (Left (\opts -> Just $ opts { optVerbosity = read f }))) "INT")
    ("Output verbosity during translation:\n" ++
    "0 - minimal output.\n" ++
    "-1 - no translation output.\n" ++
    "1 (default) - translator/simulator log.\n" ++
    "2 - translator trace (on exception).\n" ++
    "3 - instruction post-processing trace (on exception).\n4 - globals collection trace.\n" ++
    "6 - translator and globals collection trace (always).")

  , Option [] ["report-success"] (NoArg (Right (\opts -> Just $ opts { reportSucceedingInstructions = True })))
    "Print list of successfully translated instructions"

  , Option [] ["report-deps"] (NoArg (Right (\opts -> Just $ opts { reportFunctionDependencies = True })))
    "Print ancestors of functions when reporting exceptions"

  , Option [] ["report-exceptions"] (NoArg (Right (\opts -> Just $ opts { reportAllExceptions = True })))
    "Print all collected exceptions thrown during translation (requires collect-exceptions or collect-expected-exceptions)"

  , Option "o" ["output-formulas"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpOutput = f} })) "PATH")

   "Path to serialized formulas."
  , Option [] ["report-expected-exceptions"] (NoArg (Right (\opts -> Just $ opts {reportKnownExceptions = True })))
    "Print collected exceptions for known issues thrown during translation (requires collect-exceptions or collect-expected-exceptions)"

  , Option [] ["translation-mode"] (ReqArg (\mode -> Left (\opts -> do
      task <- ASL.getTranslationMode mode
      return $ opts { optFilters = task (optFilters opts) })) "TRANSLATION_MODE")
    ("Filter instructions according to TRANSLATION_MODE: \n" ++
     "all - translate all instructions.\n" ++
     "noArch64 - translate T16, T32 and A32 instructions.\n" ++
     "Arch32 (default) - translate T32 and A32 instructions.\n" ++
     "<INSTRUCTION>/<ENCODING> - translate a single instruction/encoding pair.")

  , Option [] ["simulation-mode"] (ReqArg (\mode -> Left (\opts -> do
      task <- ASL.getSimulationMode mode
      return $ opts { optFilters = task (optFilters opts) })) "SIMULATION_MODE")
    ("Filter instructions and functions for symbolic simulation according to SIMULATION_MODE: \n" ++
     "all (default) - simulate all successfully translated instructions and functions. \n" ++
     "instructions - simulate only instructions. \n" ++
     "none - do not perform any symbolic execution.")

  , Option [] ["no-dependencies"] (NoArg (Left (\opts -> Just $ opts { optTranslationDepth = TranslateShallow } )))
    "Don't recursively translate function dependencies."

  , Option [] ["check-serialization"] (NoArg (Left (\opts -> Just $ opts { optCheckSerialization = True } )))
    "Check that serialization/deserialization for any processed formulas is correct."
  ]




