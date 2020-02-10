{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Main ( main ) where

import           Data.Parameterized.Nonce
import           Data.Parameterized.Some ( Some(..) )
import qualified What4.Serialize.Parser as WP
import qualified What4.Utils.Log as U
import qualified What4.Utils.Util as U
import qualified What4.Expr.Builder as B
import           Control.Monad.IO.Class
import           System.IO

formulasFile :: FilePath
formulasFile = "./output/formulas.what4"

main :: IO ()
main = readFormulas formulasFile

data BuilderData t = NoBuilderData

readFormulas :: FilePath -> IO ()
readFormulas path = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr NoBuilderData r
  lcfg <- U.mkLogCfg "check serialization"
  U.withLogCfg lcfg $
    WP.readSymFnEnvFromFile (WP.defaultParserConfig sym) path >>= \case
      Left err -> fail err
      Right _ -> return ()
