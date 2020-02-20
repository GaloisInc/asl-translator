{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.ASL.Formulas.Attach
  ( attachFormulasSrc
  , loadFormulasSrc
  , decodeSrc
  ) where

import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Unsafe as UBS
import qualified System.IO.Unsafe as IO
import qualified Codec.Compression.GZip as GZ

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

loadFormulasSrc :: FilePath -> IO BS.ByteString
loadFormulasSrc fs = do
  t <- T.readFile fs
  let bs = T.encodeUtf8 t
  return $ LBS.toStrict $ GZ.compress $ LBS.fromStrict bs

decodeSrc :: BS.ByteString -> T.Text
decodeSrc bs = T.decodeUtf8 $ LBS.toStrict $ GZ.decompress $ LBS.fromStrict bs

attachFormulasSrc :: FilePath -> TH.ExpQ
attachFormulasSrc fp = do
  TH.qAddDependentFile fp
  t <- TH.runIO $ loadFormulasSrc fp
  embedByteString t

embedByteString :: BS.ByteString -> TH.ExpQ
embedByteString bs =
  [| IO.unsafePerformIO (UBS.unsafePackAddressLen len $(TH.litE (TH.StringPrimL (BS.unpack bs)))) |]
  where
    len = BS.length bs
