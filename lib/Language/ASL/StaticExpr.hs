{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Language.ASL.StaticExpr
  (
    StaticValue(..)
  , StaticType(..)
  , StaticValues
  , StaticEnvMap(..)
  , StaticEnv
  , typeOfStatic
  , staticEnvValue
  , staticEnvType
  , bitsToInteger
  , integerToBits
  , applyTypeSynonyms
  , simpleStaticEnvMap
  , applyStaticEnv
  , emptyStaticEnvMap
  , insertStaticEnv
  , exprToStatic
  , getPossibleVarValues
  , staticBinding
  , unstaticBinding
  , staticToExpr
  )
where

import           Math.NumberTheory.Logarithms
import           Control.Monad
import qualified Control.Monad.Fail as Fail
import           Control.Applicative
import qualified Language.ASL.Syntax as AS
import qualified Data.Text as T
import           Data.List (nub)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import           Data.Maybe (catMaybes)
import           Language.ASL.Types
import qualified Language.ASL.SyntaxTraverse as AS ( pattern VarName )
import           Data.Foldable ( traverse_ )


bitsToInteger :: [Bool] -> Integer
bitsToInteger [x] = fromIntegral (fromEnum x)
bitsToInteger [] = error $ "bitsToInteger empty list"
bitsToInteger xs = let
  (half, _) = length xs `divMod` 2
  (first, second) = List.splitAt half xs
  firstInt = bitsToInteger first
  secondInt = bitsToInteger second
  in (firstInt * 2 ^ (length second)) + secondInt


integerToBits :: Integer -> Integer -> [Bool]
integerToBits len val =
  if length (go val) <= (fromIntegral len) then
    reverse $ take (fromIntegral len) (go val ++ repeat False)
  else
    error $ "integerToBits: Integer: " ++ show val ++ " is too large for a bitvector of length: " ++ show len
  where
    go :: Integer -> [Bool]
    go 0 = []
    go val' | val' > 0 =
      let
        (half, rem_) = val' `divMod` 2
      in (rem_ == 1) : go half
    go _ = error $ "integerToBits: Unsupported negative int:" ++ show val

-- TODO: Type synonyms are currently a global property,
-- ideally type normalization should happen with respect to
-- some typing environment so this can be generated from the above.

-- We can't treat these as normal aliases, since we need to retain the
-- register field information.
globalTypeSynonyms :: [(T.Text, AS.Type)]
globalTypeSynonyms =
  [ ("CPACRType", bits 32)
  , ("CNTKCTLType", bits 32)
  , ("ESRType", bits 32)
  , ("FPCRType", bits 32)
  , ("MAIRType", bits 64)
  , ("SCRType", bits 32)
  , ("SCTLRType", bits 64)
  ]
  where bits n = AS.TypeFun "bits" (AS.ExprLitInt  n)


data StaticValue =
    StaticInt Integer
  | StaticBool Bool
  | StaticBV AS.BitVector
  deriving (Eq, Ord)

instance Show StaticValue where
  show t = case t of
    StaticInt i -> show i
    StaticBool b -> show b
    StaticBV bv -> show bv

data StaticType =
    StaticBVType Integer
  | StaticIntType
  | StaticBoolType
  deriving (Show, Eq)

typeOfStatic :: StaticValue -> StaticType
typeOfStatic sv = case sv of
  StaticInt _ -> StaticIntType
  StaticBool _ -> StaticBoolType
  StaticBV bv -> StaticBVType (fromIntegral $ length bv)

class StaticEnv a where
  staticEnvValue :: a -> T.Text -> Maybe StaticValue
  staticEnvType :: a -> T.Text -> Maybe StaticType

type StaticValues = Map.Map T.Text StaticValue

data StaticEnvMap = StaticEnvMap
  { staticEnvMapVals :: StaticValues
  , staticEnvMapTypes :: T.Text -> Maybe StaticType
  }

instance StaticEnv StaticEnvMap where
  staticEnvValue (StaticEnvMap vars _) nm = Map.lookup nm vars
  staticEnvType (StaticEnvMap vars types) nm = case Map.lookup nm vars of
    Just sv -> Just $ typeOfStatic sv
    _ -> types nm

emptyStaticEnvMap :: StaticEnvMap
emptyStaticEnvMap = simpleStaticEnvMap Map.empty

simpleStaticEnvMap :: StaticValues -> StaticEnvMap
simpleStaticEnvMap vals = StaticEnvMap vals (\_ -> Nothing)

data EnvPEntry =
    EnvPValue StaticValue
  | EnvPInfeasable StaticType (Set.Set StaticValue)
  deriving (Eq, Show)

data StaticEnvP = StaticEnvP { unStaticEnvP :: Map.Map T.Text EnvPEntry }
  deriving (Eq, Show)

emptyStaticEnvP :: StaticEnvP
emptyStaticEnvP = StaticEnvP Map.empty

instance StaticEnv StaticEnvP where
  staticEnvValue (StaticEnvP entries) nm = case Map.lookup nm entries of
    Just (EnvPValue sv) -> Just sv
    _ -> Nothing
  staticEnvType (StaticEnvP entries) nm = case Map.lookup nm entries of
    Just (EnvPInfeasable st _) -> Just st
    Just (EnvPValue sv) -> Just $ typeOfStatic sv
    _ -> Nothing

liftStaticEnvP :: (Map.Map T.Text EnvPEntry -> Map.Map T.Text EnvPEntry) -> StaticEnvP -> StaticEnvP
liftStaticEnvP f (StaticEnvP env) = StaticEnvP (f env)

insertStaticEnv :: T.Text -> StaticValue -> StaticEnvMap -> StaticEnvMap
insertStaticEnv nm v (StaticEnvMap vals types) =
  StaticEnvMap (Map.insert nm v vals) types


exprToStaticType :: StaticEnv env
                 => env
                 -> AS.Expr
                 -> Maybe StaticType
exprToStaticType env expr = case expr of
  AS.ExprVarRef (AS.QualifiedIdentifier _ ident) -> staticEnvType env ident
  AS.ExprIf ((_, body) : rest) fin ->
    case exprToStaticType env body of
      Just t -> Just t
      Nothing -> exprToStaticType env (AS.ExprIf rest fin)
  AS.ExprIf [] fin -> exprToStaticType env fin
  AS.ExprLitBin bv -> Just $ StaticBVType (fromIntegral $ length bv)
  AS.ExprBinOp AS.BinOpConcat e' e'' -> do
    StaticBVType t' <- exprToStaticType env e'
    StaticBVType t'' <- exprToStaticType env e''
    return $ StaticBVType $ t' + t''
  AS.ExprSlice _ [AS.SliceRange hi lo] -> do
    StaticInt hi' <- exprToStatic env hi
    StaticInt lo' <- exprToStatic env lo
    return $ StaticBVType ((hi' - lo') + 1)
  AS.ExprSlice _ [AS.SliceSingle _] -> Just $ StaticBVType 1
  AS.ExprSlice _ [AS.SliceOffset _ offset] -> do
    StaticInt offset' <- exprToStatic env offset
    return $ StaticBVType offset'
  AS.ExprSlice e (slice : rest) -> do
    StaticBVType rest' <- exprToStaticType env $ AS.ExprSlice e rest
    StaticBVType slice' <- exprToStaticType env $ AS.ExprSlice e [slice]
    return $ StaticBVType (rest' + slice')
  _ -> Nothing

staticBinOp :: AS.BinOp
            -> Maybe StaticValue
            -> Maybe StaticValue
            -> Maybe StaticValue
staticBinOp bop msv msv' = do
  sv <- msv
  sv' <- msv'
  case bop of
    AS.BinOpEQ -> return $ StaticBool $ sv == sv'
    AS.BinOpNEQ -> return $ StaticBool $ sv /= sv'
    _ -> fail ""
  <|> do
  StaticInt i <- msv
  StaticInt i' <- msv'
  let resultI primop = return $ StaticInt $ primop i i'
  let resultB primop = return $ StaticBool $ primop i i'
  let divI =
        let
          (quotient, remainder) = (i `divMod` i')
        in if remainder == 0 then return $ StaticInt quotient
        else fail ""
  case bop of
      AS.BinOpAdd -> resultI (+)
      AS.BinOpSub -> resultI (-)
      AS.BinOpMul -> resultI (*)
      AS.BinOpPow -> resultI (^)
      AS.BinOpDiv -> divI
      AS.BinOpDivide -> divI
      AS.BinOpShiftLeft -> resultI (\base -> \shift -> base * (2 ^ shift))
      AS.BinOpGT -> resultB (>)
      AS.BinOpLT -> resultB (<)
      AS.BinOpGTEQ -> resultB (>=)
      AS.BinOpLTEQ -> resultB (<=)
      _ -> fail ""
  <|> do
  case bop of
    AS.BinOpLogicalAnd -> do
      StaticBool False <- msv
      return $ StaticBool False
      <|> do
      StaticBool False <- msv'
      return $ StaticBool False
      <|> do
      StaticBool True <- msv
      StaticBool True <- msv'
      return $ StaticBool True
    AS.BinOpLogicalOr -> do
      StaticBool True <- msv
      return $ StaticBool True
      <|> do
      StaticBool True <- msv'
      return $ StaticBool True
      <|> do
      StaticBool False <- msv
      StaticBool False <- msv'
      return $ StaticBool False
    _ -> fail ""
  <|> do
  AS.BinOpConcat <- return $ bop
  StaticBV bv <- msv
  StaticBV bv' <- msv'
  return $ StaticBV $ bv ++ bv'


exprToStatic :: StaticEnv env
             => env
             -> AS.Expr
             -> Maybe StaticValue
exprToStatic env expr = case expr of
  AS.ExprIf ((test, body) : rest) fin -> do
    exprToStatic env test >>= \case
      StaticBool True -> exprToStatic env body
      StaticBool False -> exprToStatic env (AS.ExprIf rest fin)
      _ -> fail ""
  AS.ExprIf [] fin -> exprToStatic env fin
  AS.ExprLitInt i -> Just $ StaticInt i
  AS.ExprLitBin bv -> Just $ StaticBV bv
  AS.ExprInMask bv mask -> do
    StaticBV bv' <- exprToStatic env bv
    return $ StaticBool $ matchMask bv' mask
  AS.ExprVarRef (AS.QualifiedIdentifier _ "TRUE") -> Just $ StaticBool True
  AS.ExprVarRef (AS.QualifiedIdentifier _ "FALSE") -> Just $ StaticBool False
  AS.ExprVarRef (AS.QualifiedIdentifier _ ident) -> staticEnvValue env ident
  AS.ExprBinOp bop e' e'' ->
    staticBinOp bop (exprToStatic env e') (exprToStatic env e'')
  AS.ExprUnOp AS.UnOpNot e' -> do
    StaticBool b <- exprToStatic env e'
    return $ StaticBool $ not b
  AS.ExprUnOp AS.UnOpNeg e' -> do
    StaticInt i <- exprToStatic env e'
    return $ StaticInt (-i)
  AS.ExprCall (AS.VarName "log2") [e'] -> do
    StaticInt i <- exprToStatic env e'
    return $ StaticInt (fromIntegral (integerLog2 i))
  AS.ExprCall (AS.QualifiedIdentifier _ "sizeOf") [e] -> do
    StaticBVType i <- exprToStaticType env e
    return $ StaticInt i
  _ -> Nothing

matchMask :: AS.BitVector -> AS.Mask -> Bool
matchMask bv mask =
  if | length bv == length mask ->
       List.all matchBit (zip bv mask)
     | otherwise -> error $ "Mismatched bitvector sizes."
  where
    matchBit = \case
      (True, AS.MaskBitSet) -> True
      (False, AS.MaskBitUnset) -> True
      (_, AS.MaskBitEither) -> True
      _ -> False

-- | Nondeterministic state monad for collecting possible variable assignments.
newtype StaticEnvM a = StaticEnvM { getStaticPEnvs :: StaticEnvP -> [(StaticEnvP, a)] }

instance Functor StaticEnvM where
  fmap f (StaticEnvM spenvs) = StaticEnvM (map (\(env', ret) -> (env', f ret)) . spenvs)

instance Applicative StaticEnvM where
  pure x = StaticEnvM (\env -> [(env, x)])
  (<*>) = ap

instance Monad StaticEnvM where
  StaticEnvM f >>= g =
    StaticEnvM (\env -> concat $ map (\(env', ret) -> getStaticPEnvs (g ret) env') (f env))

instance Fail.MonadFail StaticEnvM where
  fail _ = StaticEnvM (\_ -> [])

instance Alternative StaticEnvM where
  empty = Fail.fail ""
  StaticEnvM x <|> StaticEnvM y = StaticEnvM (\env -> (x env) ++ (y env))

instance MonadPlus StaticEnvM

-- | Restricted alternative where results for the second alternative are only
-- considered if the first alternative produces no results.
tryCatchEnv :: StaticEnvM a -> StaticEnvM a -> StaticEnvM a
tryCatchEnv (StaticEnvM f) (StaticEnvM g) = StaticEnvM (\env -> case f env of {[] -> g env; x -> x})

-- | Absorb nondeterministic failure as a no-op instead
maybeEnv :: StaticEnvM () -> StaticEnvM ()
maybeEnv f = tryCatchEnv f (return ())

runStaticEnvM ::  StaticEnvP -> StaticEnvM a -> [(StaticEnvP, a)]
runStaticEnvM env (StaticEnvM f) = f env

getEnv :: StaticEnvM StaticEnvP
getEnv = StaticEnvM (\env -> [(env, env)])

modifyEnv :: (StaticEnvP -> StaticEnvP) -> StaticEnvM ()
modifyEnv f = StaticEnvM (\env -> [(f env, ())])

setStaticValue :: T.Text -> StaticValue -> StaticEnvM ()
setStaticValue nm sv =
  modifyEnv (liftStaticEnvP $ Map.insert nm (EnvPValue sv))

-- | Set the given variable to have a known type, with no infeasable values.
-- Bitvectors with a known length will be nondeterministically
-- expanded to all possible bitvectors of that length
setVariableType :: T.Text -> StaticType -> StaticEnvM ()
setVariableType nm stp = modifyEnv $ liftStaticEnvP $ Map.insert nm (EnvPInfeasable stp Set.empty)

setInfeasableValue :: T.Text -> StaticValue -> StaticEnvM ()
setInfeasableValue nm sv =
  modifyEnv (liftStaticEnvP $ Map.alter upd nm)
  where
    upd (Just (EnvPInfeasable ty svs)) = Just (EnvPInfeasable ty (Set.insert sv svs))
    upd Nothing = Just (EnvPInfeasable (typeOfStatic sv) (Set.singleton sv))
    upd (Just (EnvPValue sv')) = Just (EnvPValue sv')

liftList :: [a] -> StaticEnvM a
liftList xs = StaticEnvM (\env -> map (\x -> (env, x)) xs)

liftMaybe :: Maybe a -> StaticEnvM a
liftMaybe (Just a) = return a
liftMaybe _ = fail ""

-- | For unknown-valued bitvectors we can nondeterministically determine
-- all possible values. To avoid a state explosion, we cap the size of
-- individual bitvectors.
possibleValuesFor :: T.Text -> StaticEnvM StaticValue
possibleValuesFor nm = do
  StaticEnvP env <- getEnv
  case Map.lookup nm env of
    Just (EnvPInfeasable (StaticBVType sz) inf) -> do
      bv' <- liftList $ allPossibleBVs sz
      let bv = StaticBV bv'
      if Set.member bv inf
        then fail ""
        else setStaticValue nm bv >> return bv
    Just (EnvPValue sv) -> return sv
    _ -> fail ""

staticValueOfVar :: T.Text -> StaticEnvM StaticValue
staticValueOfVar nm = do
  StaticEnvP env <- getEnv
  case Map.lookup nm env of
    Just (EnvPValue sv) -> return sv
    _ -> fail ""

assertEquality :: Bool -> AS.Expr -> AS.Expr -> StaticEnvM ()
assertEquality positive expr1 expr2 =
  case expr1 of
    AS.ExprVarRef (AS.VarName nm) -> do
      sv <- exprToStaticM expr2
      if positive then setStaticValue nm sv
      else setInfeasableValue nm sv
    -- AS.ExprBinOp AS.BinOpConcat e1 e2 -> do
    --   StaticBV bv <- exprToStaticM expr2
    --   env <- getEnv
    --   maybeEnv $ do
    --     split <- tryCatchEnv
    --       (do
    --           StaticBVType e1sz <- liftMaybe $ exprToStaticType env e1
    --           return $ fromIntegral e1sz)
    --       (do
    --           StaticBVType e2sz <- liftMaybe $ exprToStaticType env e2
    --           return (length bv - (fromIntegral e2sz)))
    --     let (bv1, bv2) = splitAt split bv
    --     maybeEnv $ assertEquality positive e1 (AS.ExprLitBin $ bv1)
    --     maybeEnv $ assertEquality positive e2 (AS.ExprLitBin $ bv2)
    _ -> fail ""

-- Where possible, produces a set of augmented environments
-- where the given expression is necessarily true
assertExpr :: Bool -> AS.Expr -> StaticEnvM ()
assertExpr positive expr = case expr of
  AS.ExprBinOp AS.BinOpEQ e e' ->
    maybeEnv $ tryCatchEnv
      (assertEquality positive e e')
      (assertEquality positive e' e)
  AS.ExprBinOp AS.BinOpNEQ e1 e2 -> assertExpr (not positive) (AS.ExprBinOp AS.BinOpEQ e1 e2)
  AS.ExprUnOp AS.UnOpNot e' -> assertExpr (not positive) e'
  AS.ExprBinOp AS.BinOpLogicalAnd e1 e2 ->
    if positive then do
      assertExpr True e1
      assertExpr True e2
    else
      assertExpr False e1 <|> assertExpr False e2
  AS.ExprBinOp AS.BinOpLogicalOr e1 e2 -> assertExpr positive $
    AS.ExprUnOp AS.UnOpNot (AS.ExprBinOp AS.BinOpLogicalAnd (AS.ExprUnOp AS.UnOpNot e1) (AS.ExprUnOp AS.UnOpNot e2))
  AS.ExprInSet e' setElts -> maybeEnv $ do
    AS.SetEltSingle e'' <- liftList $ setElts
    assertExpr positive (AS.ExprBinOp AS.BinOpEQ e' e'')
  _ -> return ()

testExpr :: AS.Expr -> StaticEnvM Bool
testExpr test = do
  StaticBool b <- tryCatchEnv (exprToStaticM test) $
        (assertExpr True test >> return (StaticBool True))
    <|> (assertExpr False test >> return (StaticBool False))
  return b

-- | Nondeterministically evaluate an expression into possible values.
-- We nondeterministically expand variables
-- into all possible assignments based on their type (restricted by
-- their infeasable values).
exprToStaticM :: AS.Expr -> StaticEnvM StaticValue
exprToStaticM expr = do
  env <- getEnv
  case exprToStatic env expr of
    Just sv -> return sv
    _ -> case expr of
      AS.ExprVarRef (AS.VarName nm) -> possibleValuesFor nm
      -- Don't speculate across concats, this quickly causes a state explosion
      AS.ExprBinOp AS.BinOpConcat _ _ -> fail ""
      AS.ExprBinOp bop e1 e2 -> do
        sv1 <- exprToStaticM e1
        sv2 <- exprToStaticM e2
        liftMaybe $ staticBinOp bop (Just sv1) (Just sv2)
      AS.ExprIf ((test, body) : rest) fin -> do
        testExpr test >>= \case
          True -> exprToStaticM body
          False -> exprToStaticM (AS.ExprIf rest fin)
      AS.ExprIf [] fin -> exprToStaticM fin
      AS.ExprCall (AS.VarName "UInt") [e] -> do
        StaticBV bv <- exprToStaticM e
        return $ StaticInt $ bitsToInteger bv
      _ -> fail ""


allPossibleBVs :: Integer -> [[Bool]]
allPossibleBVs 1 = [[True], [False]]
allPossibleBVs n = do
  bit <- [True, False]
  bits <- allPossibleBVs (n - 1)
  return $ bit : bits

-- | Get all possible variable assignments for the given variables after
-- the provided set of statements has been evaluated
getPossibleVarValues :: [(T.Text, StaticType)] -- ^ initial known variable types
                     -> [T.Text] -- ^ mandatory variables
                     -> [T.Text] -- ^ optional variables
                     -> [AS.Stmt] -- ^ evaluated statements
                     -> [Map.Map T.Text StaticValue] -- ^ Possible binding environments
getPossibleVarValues vartps vars optvars stmts =
  let results = map snd $ runStaticEnvM emptyStaticEnvP $ do
        traverse_ (uncurry $ setVariableType) vartps
        stmtsToStaticM stmts
        svs <- mapM staticValueOfVar vars
        optsvs <- mapM maybeVar optvars
        return $ (zip vars svs) ++ catMaybes optsvs
  in nub $ map Map.fromList results
  where
    maybeVar var =
      tryCatchEnv
        ((\sv -> Just (var, sv)) <$> staticValueOfVar var)
        (return Nothing)

stmtsToStaticM :: [AS.Stmt] -> StaticEnvM ()
stmtsToStaticM stmts = traverse_ stmtToStaticM stmts

stmtToStaticM :: AS.Stmt -> StaticEnvM ()
stmtToStaticM s = case s of
  AS.StmtCall (AS.VarName "ASLSetUndefined") [] -> fail ""
  AS.StmtCall (AS.VarName "ASLSetUnpredictable") [] -> fail ""

  AS.StmtAssert e -> assertExpr True e

  AS.StmtIf tests fin -> applyTests tests fin

  AS.StmtAssign (AS.LValVarRef (AS.VarName nm)) e -> maybeEnv $ do
    sv <- exprToStaticM e
    setStaticValue nm sv

  AS.StmtVarDeclInit (nm, _)  e -> maybeEnv $ do
    sv <- exprToStaticM e
    setStaticValue nm sv

  AS.StmtCase test cases ->
    let (tests, fin) = casesToTests test cases
    in applyTests tests fin
  _ -> return ()
  where
    applyTests tests mfin = case tests of
      (test, body) : rest -> do
        testExpr test >>= \case
          True -> stmtsToStaticM body
          False -> applyTests rest mfin
      _ -> case mfin of
        Just fin -> stmtsToStaticM fin
        _ -> return ()

    casesToTests e = \case
      (AS.CaseWhen (pat : pats) _ stmts) : rest -> let
        (tests, fin) = casesToTests e rest
        test = foldr (\pat' -> \e' -> AS.ExprBinOp AS.BinOpLogicalOr e' (patToExpr e pat')) (patToExpr e pat) pats
        in ((test, stmts) : tests, fin)
      [AS.CaseOtherwise stmts] -> ([], Just stmts)
      [] -> ([], Nothing)
      _ -> error $ "Unexpected case format: " ++ show e

    patToExpr e pat = case pat of
      AS.CasePatternInt i -> AS.ExprBinOp AS.BinOpEQ e (AS.ExprLitInt i)
      AS.CasePatternBin bv -> AS.ExprBinOp AS.BinOpEQ e (AS.ExprLitBin bv)
      AS.CasePatternMask mask -> AS.ExprInMask e mask
      AS.CasePatternIdentifier ident -> AS.ExprBinOp AS.BinOpEQ (AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny ident)) e
      _ -> AS.ExprUnknown (AS.TypeRef (AS.QualifiedIdentifier AS.ArchQualAny "boolean"))


applyTypeSynonyms :: AS.Type -> AS.Type
applyTypeSynonyms t = case t of
  AS.TypeRef (AS.QualifiedIdentifier _ tpName) ->
    case lookup tpName globalTypeSynonyms of
      Just syn -> syn
      Nothing -> t
  _ -> t

applyStaticEnv :: StaticEnv env
                => env
                -> AS.Type
                -> Maybe AS.Type
applyStaticEnv env t = case applyTypeSynonyms t of
  AS.TypeFun "bits" e -> case exprToStatic env e of
    Just (StaticInt i) -> Just $ AS.TypeFun "bits" (AS.ExprLitInt i)
    _ -> Nothing
  AS.TypeArray t' idxt -> do
    t'' <- applyStaticEnv env t'
    return $ AS.TypeArray t'' idxt
  _ -> Just $ t


staticToExpr :: StaticValue -> AS.Expr
staticToExpr sv = case sv of
  StaticInt i -> AS.ExprLitInt i
  StaticBool True -> trueExpr
  StaticBool False -> falseExpr
  StaticBV bv -> AS.ExprLitBin bv

staticBinding :: (T.Text, StaticValue) -> AS.Stmt
staticBinding (nm, sv) =
  AS.StmtCall (AS.QualifiedIdentifier AS.ArchQualAny "StaticBind")
    [AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny nm), staticToExpr sv]

unstaticBinding :: StaticEnv env => AS.Stmt -> Maybe (env -> (T.Text, StaticValue))
unstaticBinding (AS.StmtCall (AS.QualifiedIdentifier _ "StaticBind") [AS.ExprVarRef (AS.QualifiedIdentifier _ nm), e]) = Just $ \env ->
  case exprToStatic env e of
    Just sv -> (nm, sv)
    _ -> error "Invalid StaticBind"
unstaticBinding _ = Nothing
