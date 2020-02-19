{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main ( main ) where

import qualified Data.Map as M
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.TraversableFC
import qualified Data.Ratio as R
import qualified Data.Text as T
import qualified What4.Interface as WI
import qualified What4.Expr.Builder as B
import qualified What4.Serialize.Parser as WP
import qualified What4.Utils.Complex as U
import qualified What4.Utils.Log as U
import qualified What4.Utils.Util as U
import qualified What4.Utils.Word16String as U
import           Control.Monad.IO.Class
import           System.Exit
import           System.Random (randomIO)

formulasFile :: FilePath
formulasFile = "./output/formulas.what4"

formulaName :: String
formulaName = "uf.HaveBTIExt_0"

main :: IO ()
main = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr NoBuilderData r
  lcfg <- U.mkLogCfg "concrete evaluation"
  U.withLogCfg lcfg $ do
    putStrLn $ "Reading formulas..."
    env <- readFormulas sym formulasFile
    putStrLn $ "Testing " <> formulaName <> " ..."
    case M.lookup (T.pack formulaName) env of
      Nothing -> do
        putStrLn $ "Could not find formula " <> formulaName <> "."
        exitFailure
      Just (U.SomeSome symFn) -> do
        let argTps = WI.fnArgTypes symFn
        args <- traverseFC (randomSymExpr sym) argTps
        putStrLn $ "Calling " <> formulaName <> " with args:"
        print args
        putStrLn "Result:"
        res <- WI.applySymFn sym symFn args
        print res

data BuilderData t = NoBuilderData

readFormulas :: (U.HasLogCfg,
                 WI.IsSymExprBuilder sym,
                 WI.IsExprBuilder sym,
                 ShowF (WI.SymExpr sym))
             => sym -> FilePath -> IO (WP.SymFnEnv sym)
readFormulas sym path = do
  WP.readSymFnEnvFromFile (WP.defaultParserConfig sym) path >>= \case
    Left err -> fail err
    Right env -> return env

-- FIXME: There is probably a better way to handle 0 denominators, but
-- this works for now.
randomRational :: IO Rational
randomRational = do
  randNum <- randomIO
  randDenom <- do
    n <- randomIO
    return (if n == 0 then 1 else n)
  return (randNum R.% randDenom)

randomSymExpr :: (WI.IsSymExprBuilder sym,
              WI.IsExprBuilder sym)
          => sym
          -> WI.BaseTypeRepr tp
          -> IO (WI.SymExpr sym tp)
randomSymExpr sym tp = case tp of
  WI.BaseBoolRepr -> do
    randBool <- randomIO
    case randBool of
      True -> return (WI.truePred sym)
      False -> return (WI.falsePred sym)
  WI.BaseBVRepr w -> do
    randInt <- randomIO
    WI.bvLit sym w randInt
  WI.BaseNatRepr -> do
    randInt <- randomIO
    WI.natLit sym (fromInteger randInt)
  WI.BaseIntegerRepr -> do
    randInt <- randomIO
    WI.intLit sym randInt
  WI.BaseRealRepr -> do
    randRat <- randomRational
    WI.realLit sym randRat
  WI.BaseFloatRepr floatPrecision -> do
    randRat <- randomRational
    WI.floatLit sym floatPrecision randRat
  WI.BaseStringRepr stringInfo -> case stringInfo of
    WI.Char8Repr -> WI.stringLit sym (WI.Char8Literal "CHAR8STRING")
    WI.Char16Repr -> WI.stringLit sym (WI.Char16Literal (U.fromLEByteString "CHAR16STRING"))
    WI.UnicodeRepr -> WI.stringLit sym (WI.UnicodeLiteral "UNICODESTRING")
  WI.BaseComplexRepr -> do
    randRealRat <- randomRational
    randCplxRat <- randomRational
    WI.mkComplexLit sym (randRealRat U.:+ randCplxRat)
  WI.BaseStructRepr fieldTps -> do
    randFields <- traverseFC (randomSymExpr sym) fieldTps
    WI.mkStruct sym randFields
  WI.BaseArrayRepr ixTps eltTp -> do
    randConst <- randomSymExpr sym eltTp
    WI.constantArray sym ixTps randConst
