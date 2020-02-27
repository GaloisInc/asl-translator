{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.ASL.Formulas
    ( getFormulas
    , FS.NamedSymFnEnv
    ) where

import qualified Data.Text as T

import           Data.Parameterized.Classes

import qualified What4.Interface as WI

import qualified What4.Serialize.Parser as WP
import qualified What4.Utils.Log as U
import           What4.Utils.Util ( SomeSome(..) )

import           Language.ASL.Formulas.Attach
import qualified Language.ASL.Formulas.Serialize as FS

formulas :: T.Text
formulas = decodeSrc $(attachFormulasSrc "./output/formulas.what4" "./archived/formulas.what4.gz")

getFormulas :: (WI.IsSymExprBuilder sym,
                WI.IsExprBuilder sym,
                ShowF (WI.SymExpr sym))
             => sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getFormulas sym env = do
  sexpr <- FS.parseSExpr formulas
  FS.deserializeSymFnEnv sym env (FS.uninterpFunctionMaker sym) sexpr
