{-|
Module           : Main
Copyright        : (c) Galois, Inc 2019-2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

The top-level executable for running the ASL translator.
See "Language.ASL.Translation.Driver" for most of
the relevant functionality.

-}

{-# LANGUAGE ScopedTypeVariables #-}

module Main ( main ) where

import           Control.Monad ( when )
import           GHC.Stack ( HasCallStack )

import qualified Data.Text as T
import qualified Data.List.Split as List

import           System.Exit (exitFailure)
import qualified System.Environment as IO
import qualified System.IO as IO
import           System.Console.GetOpt

import           Language.ASL.Translation.Driver ( TranslatorOptions(..), StatOptions(..)
                                                 , FilePathConfig(..), TranslationDepth(..)
                                                 , NormalizeMode(..)
                                                 )
import qualified Language.ASL.Translation.Driver as ASL

import qualified What4.Serialize.Log as Log

import Debug.Trace

main :: HasCallStack => IO ()
main = do
  nonLogCfg <- Log.mkNonLogCfg
  stringArgs <- IO.getArgs
  let (args, rest, errs) = getOpt Permute arguments stringArgs

  when (not $ null $ errs <> rest) $ do
    usage
    exitFailure

  case foldl applyOption (Just (ASL.defaultOptions nonLogCfg, ASL.defaultStatOptions)) args of
    Nothing -> do
      usage
      exitFailure
    Just (opts', statOpts) -> case optNormalizeMode opts' of
      NormalizeNone -> runTranslator opts' statOpts
      _ -> Log.withLogging "main" (logEventConsumer opts') $ do
        let opts = opts' { optLogCfg = Log.getLogCfg }
        ASL.readAndNormalize opts
  where
    applyOption (Just (opts, statOpts)) arg = case arg of
      Left f -> do
        opts' <- f opts
        return $ (opts', statOpts)
      Right f -> do
        statOpts' <- f statOpts
        return $ (opts, statOpts')
    applyOption Nothing _ = Nothing

runTranslator :: TranslatorOptions -> StatOptions -> IO ()
runTranslator opts' statOpts = do
  Log.withLogging "main" (logEventConsumer opts') $ do
    let opts = opts' { optLogCfg = Log.getLogCfg }
    sm <- ASL.translateAndSimulate opts
    ASL.reportStats statOpts sm
    ASL.serializeFormulas opts sm

logEventConsumer :: TranslatorOptions -> Log.LogCfg -> IO ()
logEventConsumer opts logCfg =
  (Log.consumeUntilEnd (intToLogLvlFilter (optVerbosity opts)) $ \e -> do
    if optVerbosity opts > 1 then
      traceIO (Log.prettyLogEvent e)
    else
      traceIO (simpleLogEvent e)
    IO.hFlush IO.stderr) logCfg
  where
    simpleLogEvent :: Log.LogEvent -> String
    simpleLogEvent le = Log.leMsg le

    intToLogLvlFilter :: Integer -> (Log.LogEvent -> Bool)
    intToLogLvlFilter i logEvent = case Log.leLevel logEvent of
      Log.Info -> i >= 1
      Log.Warn -> i >= 1
      Log.Debug -> i >= 2
      Log.Error -> True

getTranslationMode :: String -> Maybe (ASL.TranslationMode)
getTranslationMode mode = case mode of
  "AArch32" -> return $ ASL.TranslateAArch32
  _ -> case List.splitOn "/" mode of
    [instr, enc] -> return $ ASL.TranslateInstruction (T.pack instr, T.pack enc)
    _ -> fail ""

getSimulationMode :: String -> Maybe (ASL.SimulationMode)
getSimulationMode mode = case mode of
  "all" -> return $ ASL.SimulateAll
  "instructions" -> return $ ASL.SimulateInstructions
  "functions" -> return $ ASL.SimulateFunctions
  "none" -> return $ ASL.SimulateNone
  _ -> case List.splitOn "/" mode of
    [instr, enc] -> return $ ASL.SimulateInstruction (T.pack instr, T.pack enc)
    _ -> fail ""

usage :: IO ()
usage = do
  pn <- IO.getProgName
  let msg = "Usage: " <> pn <> " [options]"
  putStrLn $ usageInfo msg arguments

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

  , Option "p" ["parallel"] (NoArg (Left (\opts -> Just $ opts { optParallel = True  })))
    "Run symbolic simulation concurrently with multiple threads."

  , Option [] ["output-global-sigs"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpOutGlobalSigs = f} })) "PATH")
   "Path to type signatures for global variables."

  , Option [] ["output-functions"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpOutFuns = f} })) "PATH")
   "Path to serialized function formulas."

  , Option [] ["output-instructions"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpOutInstrs = f} })) "PATH")
   "Path to serialized instruction formulas."

  , Option [] ["output-norm-functions"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpNormFuns = f} })) "PATH")
   "Path to serialized function formulas."

  , Option [] ["output-norm-instructions"]
    (ReqArg (\f -> Left (\opts -> Just $ opts { optFilePaths = (optFilePaths opts){ fpNormInstrs = f} })) "PATH")
   "Path to serialized instruction formulas."


  , Option [] ["report-expected-exceptions"] (NoArg (Right (\opts -> Just $ opts {reportKnownExceptions = True })))
    "Print collected exceptions for known issues thrown during translation (requires collect-exceptions or collect-expected-exceptions)"

  , Option [] ["translation-mode"] (ReqArg (\mode -> Left (\opts -> do
      tmode <- getTranslationMode mode
      return $ opts { optTranslationMode = tmode })) "TRANSLATION_MODE")
    ("Filter instructions according to TRANSLATION_MODE: \n" ++
     "Arch32 (default) - translate T16, T32 and A32 instructions.\n" ++
     "<INSTRUCTION>/<ENCODING> - translate a single instruction/encoding pair.")

  , Option [] ["simulation-mode"] (ReqArg (\mode -> Left (\opts -> do
      smode <- getSimulationMode mode
      return $ opts { optSimulationMode = smode })) "SIMULATION_MODE")
    ("Filter instructions and functions for symbolic simulation according to SIMULATION_MODE: \n" ++
     "all (default) - simulate all successfully translated instructions and functions. \n" ++
     "instructions - simulate only instructions. \n" ++
     "functions - simulate only functions. \n" ++
     "none - do not perform any symbolic execution.")

  , Option [] ["no-dependencies"] (NoArg (Left (\opts -> Just $ opts { optTranslationDepth = TranslateShallow } )))
    "Don't recursively translate function dependencies."

  , Option [] ["check-serialization"] (NoArg (Left (\opts -> Just $ opts { optCheckSerialization = True } )))
    "Check that serialization/deserialization for any processed formulas is correct."

  , Option "n" ["normalize-mode"]
    (ReqArg (\mode -> Left (\opts -> do
      nmode <- case mode of
        "all" -> return $ NormalizeAll
        "only-funs" -> return $ NormalizeFunctions
        "none" -> return $ NormalizeNone
        _ -> fail ""
      return $ opts { optNormalizeMode = nmode })) "NORMALIZE_MODE")
    ("Read in the formula environment and normalize according to NORMALIZE_MODE: \n" ++
     "all - normalize both the instruction and function formulas files \n" ++
     "only-funs - only normalize the function formulas file. \n" ++
     "none (default) - do not normalize")
  ]




