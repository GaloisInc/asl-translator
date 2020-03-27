{-|
Module           : Language.ASL.Formulas
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This module provides an interface to the translated ASL
semantics, represented as a library of what4 expressions.


-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.ASL.Formulas
    ( getFunctionFormulas
    , getInstructionFormulas
    , FS.NamedSymFnEnv
    ) where

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified System.Directory as D

import           Data.Parameterized.Classes
import qualified What4.Interface as WI
import           What4.Utils.Util ( SomeSome(..) )
import qualified System.IO as IO
import qualified Codec.Compression.GZip as GZ

import qualified Language.ASL.Formulas.Serialize as FS
import           Paths_asl_translator as P

#ifdef ASL_LITE
functionFormulas :: (FilePath, FilePath)
functionFormulas = ("./output/functions-norm-lite.what4", "./archived/functions-norm-lite.what4.gz")

instructionFormulas :: (FilePath, FilePath)
instructionFormulas = ("./output/instructions-norm-lite.what4", "./archived/instructions-norm-lite.what4.gz")
#else
functionFormulas :: (FilePath, FilePath)
functionFormulas = ("./output/functions-norm.what4", "./archived/functions-norm.what4.gz")

instructionFormulas :: (FilePath, FilePath)
instructionFormulas = ("./output/instructions-norm.what4", "./archived/instructions-norm.what4.gz")
#endif


decodeSrc :: BS.ByteString -> T.Text
decodeSrc bs = T.decodeUtf8 $ LBS.toStrict $ GZ.decompress $ LBS.fromStrict bs

fileCases :: FilePath -> FilePath -> (IO.Handle -> IO a) -> (IO.Handle -> IO a) -> IO a
fileCases fp fallback f1 f2 = do
  D.doesFileExist fp >>= \case
    True -> (IO.withFile fp IO.ReadMode $ \handle -> do
      sz <- IO.hFileSize handle
      if sz > 0 then
        Just <$> f1 handle
      else return Nothing) >>= \case
        Just result -> return result
        Nothing -> IO.withFile fallback IO.ReadMode f2
    False -> IO.withFile fallback IO.ReadMode f2


genGetFormulas :: forall sym
                . (WI.IsSymExprBuilder sym,
                  WI.IsExprBuilder sym,
                  ShowF (WI.SymExpr sym))
               => (String, String) -> sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
genGetFormulas (fp', fallbackfp') sym env  = do
  fp <- P.getDataFileName fp'
  fallbackfp <- P.getDataFileName fallbackfp'
  fileCases fp fallbackfp
    (\handle -> T.hGetContents handle >>= doParse)
    (\handle -> (decodeSrc <$> BS.hGetContents handle) >>= doParse)
  where
    doParse :: T.Text -> IO [(T.Text, SomeSome (WI.SymFn sym))]
    doParse src = do
      sexpr <- FS.parseSExpr src
      FS.deserializeSymFnEnv sym env (FS.uninterpFunctionMaker sym) sexpr

-- | Given an initial function binding environment (i.e. for
-- providing bindings for uninterpreted functions), read in the
-- helper functions used in the specifications for the ARM instructions.
getFunctionFormulas :: (WI.IsSymExprBuilder sym,
                       WI.IsExprBuilder sym,
                       ShowF (WI.SymExpr sym))
                    => sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getFunctionFormulas = genGetFormulas functionFormulas


-- | Given a function environment (i.e. as read in from 'getFunctionFormulas'), read in
-- the functions that represent the semantics for each ARM instruction.
getInstructionFormulas :: (WI.IsSymExprBuilder sym,
                           WI.IsExprBuilder sym,
                           ShowF (WI.SymExpr sym))
                       => sym -> FS.NamedSymFnEnv sym -> IO [(T.Text, SomeSome (WI.SymFn sym))]
getInstructionFormulas = genGetFormulas instructionFormulas
