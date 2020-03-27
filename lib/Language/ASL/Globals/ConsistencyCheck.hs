{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.ASL.Globals.ConsistencyCheck
  (
  ) where

import           Control.Monad ( unless )
import qualified Language.ASL.Globals as G
import qualified Language.Haskell.TH as TH
import qualified System.IO as IO

$(TH.runIO $ do
     unless G.consistencyCheck $ do
       fail "Globals consistency check failed."
     IO.putStrLn "Globals consistency check passed."
     return []
 )
