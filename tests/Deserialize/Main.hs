{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Main ( main ) where

import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Map as Map
import qualified What4.Expr.Builder as B
import           Control.Monad.IO.Class
import qualified Language.ASL.Formulas as ASL

data BuilderData t = NoBuilderData

main :: IO ()
main = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr NoBuilderData r
  _ <- ASL.getFormulas sym Map.empty
  return ()
