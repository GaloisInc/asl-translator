{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}

module Language.ASL.Formulas
    ( getFunctionFormulas
    , getInstructionFormulas
    , FS.NamedSymFnEnv
    ) where

import qualified Data.Text as T

import           Data.Parameterized.Classes

import qualified What4.Interface as WI
import           What4.Utils.Util ( SomeSome(..) )

import           Language.ASL.Formulas.Attach
import qualified Language.ASL.Formulas.Serialize as FS


functionFormulas :: T.Text
functionFormulas = decodeSrc $(attachFormulasSrc "./output/functions-norm.what4" "./archived/functions-norm.what4.gz")

instructionFormulas :: T.Text
#ifdef ASL_LITE
instructionFormulas = decodeSrc $(attachFormulasSrc "./output/instructions-norm-lite.what4" "./archived/instructions-norm-lite.what4.gz")
#else
instructionFormulas = decodeSrc $(attachFormulasSrc "./output/instructions-norm.what4" "./archived/instructions-norm.what4.gz")
#endif

genGetFormulas :: (WI.IsSymExprBuilder sym,
                  WI.IsExprBuilder sym,
                  ShowF (WI.SymExpr sym))
               => T.Text -> sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
genGetFormulas src sym env  = do
  sexpr <- FS.parseSExpr src
  FS.deserializeSymFnEnv sym env (FS.uninterpFunctionMaker sym) sexpr

getFunctionFormulas :: (WI.IsSymExprBuilder sym,
                       WI.IsExprBuilder sym,
                       ShowF (WI.SymExpr sym))
                    => sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getFunctionFormulas sym = genGetFormulas functionFormulas sym

getInstructionFormulas :: (WI.IsSymExprBuilder sym,
                           WI.IsExprBuilder sym,
                           ShowF (WI.SymExpr sym))
                       => sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getInstructionFormulas sym env = genGetFormulas instructionFormulas sym env
