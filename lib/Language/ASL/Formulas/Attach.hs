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
import qualified System.IO as IO
import qualified System.IO.Unsafe as IO
import qualified System.Directory as D
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

-- | If the first file exists, assume it is plaintext - so read it in and gzip it.
-- If it does not exist, use the backup (assumed to already be gzipped)
attachFormulasSrc :: FilePath -> FilePath -> TH.ExpQ
attachFormulasSrc fp fallbackfp = do
  bs <- TH.runIO $ fileCases fp fallbackfp
    (\handle -> do
        t <- T.hGetContents handle
        return $ LBS.toStrict $ GZ.compress $ LBS.fromStrict $ T.encodeUtf8 t)
    (\handle -> do
        T.writeFile fp T.empty
        BS.hGetContents handle)
  TH.qAddDependentFile fallbackfp
  TH.qAddDependentFile fp
  embedByteString bs


embedByteString :: BS.ByteString -> TH.ExpQ
embedByteString bs =
  [| IO.unsafePerformIO (UBS.unsafePackAddressLen len $(TH.litE (TH.StringPrimL (BS.unpack bs)))) |]
  where
    len = BS.length bs
