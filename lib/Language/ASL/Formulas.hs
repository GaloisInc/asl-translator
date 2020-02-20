{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.ASL.Formulas
    ( getFormulas
    ) where

import qualified Data.Text as T

import           Data.Parameterized.Classes

import qualified What4.Interface as WI

import qualified What4.Serialize.Parser as WP
import qualified What4.Utils.Log as U
import           What4.Utils.Util ( SomeSome(..) )

import           Language.ASL.Formulas.Attach

formulas :: T.Text
formulas = decodeSrc $(attachFormulasSrc "./output/formulas.what4")


getFormulas :: (WI.IsSymExprBuilder sym,
                WI.IsExprBuilder sym,
                ShowF (WI.SymExpr sym))
             => sym -> WP.SymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getFormulas sym env = do
  let pcfg = (WP.defaultParserConfig sym) {WP.pSymFnEnv = env}
  U.withLogging "asl-translator"
    (U.stdErrLogEventConsumer (\le -> U.leLevel le >= U.Warn)) $
      WP.readSymFnList pcfg formulas >>= \case
        Left err -> fail err
        Right env' -> return env'
