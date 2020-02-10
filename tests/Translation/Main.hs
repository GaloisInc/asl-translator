module Main ( main ) where

import           Data.Maybe ( fromJust )
import           Language.ASL.Translation.Driver ( TranslatorOptions(..)
                                                 , FilePathConfig(..), TranslationDepth(..)
                                                 )
import qualified Language.ASL.Translation.Driver as ASL
import qualified What4.Utils.Log as Log


main :: IO ()
main = do
  Log.withLogging "main" (Log.stdErrLogEventConsumer logLvl) $ do
    let opts = defaultTestOptions Log.getLogCfg
    ASL.SomeSigMap sm <- ASL.runWithFilters opts
    ASL.serializeFormulas opts sm

logLvl :: Log.LogEvent -> Bool
logLvl le = case Log.leLevel le of
  Log.Error -> True
  _ -> False

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

defaultTestOptions :: Log.LogCfg -> TranslatorOptions
defaultTestOptions logCfg = TranslatorOptions
  { optVerbosity = 1
  , optStartIndex = 0
  , optNumberOfInstructions = Nothing
  , optFilters = (fromJust $ ASL.getTranslationMode "Arch32") ASL.noFilter
  , optCollectAllExceptions = False
  , optCollectExpectedExceptions = True
  , optTranslationDepth = TranslateRecursive
  , optCheckSerialization = True
  , optFilePaths = defaultFilePaths
  , optLogCfg = logCfg
  }
