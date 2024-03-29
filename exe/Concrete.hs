{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main ( main ) where

import qualified Data.BitVector.Sized as BV
import qualified Data.Map as M
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.SomeSome as U
import           Data.Parameterized.TraversableFC
import qualified Data.Ratio as R
import qualified Data.Text as T
import qualified LibBF as BF
import qualified What4.Interface as WI
import qualified What4.Expr as B
import qualified What4.Utils.Complex as U
import qualified What4.Utils.Word16String as U
import           Control.Monad.IO.Class
import           System.Exit
import           System.Random (randomIO)

import qualified Language.ASL.Formulas as FS

formulaName :: String
formulaName = "uf.HaveBTIExt_0"

main :: IO ()
main = do
  Some r <- liftIO $ newIONonceGenerator
  sym <- liftIO $ B.newExprBuilder B.FloatRealRepr B.EmptyExprBuilderState r
  putStrLn $ "Reading formulas..."
  env <- M.fromList <$> FS.getFunctionFormulas sym M.empty
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
    WI.bvLit sym w (BV.mkBV w randInt)
  WI.BaseIntegerRepr -> do
    randInt <- randomIO
    WI.intLit sym randInt
  WI.BaseRealRepr -> do
    randRat <- randomRational
    WI.realLit sym randRat
  WI.BaseFloatRepr floatPrecision -> do
    randDbl <- randomIO
    WI.floatLit sym floatPrecision (BF.bfFromDouble randDbl)
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
