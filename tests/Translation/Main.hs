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
    let opts = (ASL.defaultOptions Log.getLogCfg) { ASL.optParallel = False, ASL.optCheckSerialization = True }
    sm <- ASL.translateAndSimulate opts
    ASL.serializeFormulas opts sm
    ASL.readAndNormalize opts { ASL.optNormalizeMode = ASL.NormalizeAll }

logLvl :: Log.LogEvent -> Bool
logLvl le = case Log.leLevel le of
  Log.Error -> True
  _ -> False
