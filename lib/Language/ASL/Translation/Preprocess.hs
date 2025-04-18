{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Language.ASL.Translation.Preprocess
  ( -- * Top-level interface
    getDefinitions
  , computeInstructionSignature
  , prepASL
  , ASLSpec(..)
  , SigState
  , SigEnv
  , SigM
  , runSigM
  , buildSigState
  , SigException(..)
  , Callable(..)
  , Definitions(..)
  , bitsToInteger
  , mkFunctionName
  , mkSignature
  , registerTypeSynonyms
  , localTypeHints
  , mkExtendedTypeData'
  , mkBaseStructRepr
  , mkFinalFunctionName
  , globalStructNames
  ) where


import           Math.NumberTheory.Logarithms
import           Control.Applicative ( (<|>), Const(..) )
import qualified Control.Monad.Fail as F
import           Control.Monad (void, unless, liftM, forM_)
import qualified Control.Monad.Identity as I
import qualified Control.Monad.Except as E
import qualified Control.Monad.RWS as RWS
import qualified Data.BitVector.Sized as BV
import           Data.Foldable ( find )
import           Data.List ( nub )
import           Data.Maybe ( maybeToList, catMaybes, fromMaybe, isJust, fromJust )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )

import qualified Data.BitMask as BM
import qualified Dismantle.ARM.ASL as DA ( Encoding(..), FieldConstraint(..) )
import qualified Dismantle.Tablegen.Patterns as BT
import qualified Data.Text as T
import           Data.Traversable (forM)
import qualified Data.Parameterized.TraversableFC as FC
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT

import qualified Language.ASL.Syntax as AS

import           Language.ASL.Signature
import           Language.ASL.Types
import           Language.ASL.StaticExpr as SE
import qualified Language.ASL.Globals as G

import qualified Language.ASL.SyntaxTraverse as TR
import qualified Language.ASL.SyntaxTraverse as AS ( pattern VarName )
import           Language.ASL.SyntaxTraverse (mkFunctionName)

import           Util.Log ( MonadLog(..), MonadLogIO, LogCfg, runMonadLogIO, unindentLog  )

data Definitions arch =
  Definitions { defSignatures :: Map.Map T.Text (SomeSimpleFunctionSignature, [AS.Stmt])
              , defTypes :: Map.Map T.Text (Some UserType)
              , defEnums :: Map.Map T.Text (Some NR.NatRepr, Integer)
              , defConsts :: Map.Map T.Text (Some ConstVal)
              , defExtendedTypes :: Map.Map T.Text ExtendedTypeData
              }

-- | Collect the definitions representing the current state
getDefinitions :: SigEnv -> SigState -> Definitions arch
getDefinitions env st =
  Definitions
    { defSignatures = (\(sig, c, _) -> (sig, callableStmts c)) <$> callableSignatureMap st
    , defTypes = userTypes st
    , defEnums = enums st
    , defConsts = consts env
    , defExtendedTypes = extendedTypeData st
   }

-- NOTE: This is clagged from types.asl, in
-- theory we could read this in instead.
registerTypeSynonyms :: [(T.Text, T.Text)]
registerTypeSynonyms =
  [ ("CPACRType", "CPACR_EL1")
  , ("CNTKCTLType", "CNTKCTL_EL1")
  , ("ESRType", "ESR_EL1")
  , ("FPCRType", "FPCR")
  , ("MAIRType", "MAIR_EL1")
  , ("SCRType", "SCR")
  , ("SCTLRType", "SCTLR_EL1")
  ]



builtinConsts :: [(T.Text, Some ConstVal)]
builtinConsts =
  [ ("TRUE", Some $ ConstVal WT.BaseBoolRepr True)
  , ("FALSE", Some $ ConstVal WT.BaseBoolRepr False)
  , ("HIGH", Some $ ConstVal (WT.BaseBVRepr (WT.knownNat @1)) (BV.one WT.knownNat))
  ]

data Callable = Callable { callableName :: AS.QualifiedIdentifier
                         , callableArgs :: [AS.SymbolDecl]
                         , callableRets :: [AS.Type]
                         , callableStmts :: [AS.Stmt]
                         }
  deriving (Eq, Show)

asCallable :: AS.Definition -> Maybe Callable
asCallable def =
  case def of
    AS.DefCallable { AS.callableName = name
                   , AS.callableArgs = args
                   , AS.callableRets = rets
                   , AS.callableStmts = stmts
                   }
      | not $ null stmts ->
      Just Callable { callableName = name
                    , callableArgs = args
                    , callableRets = rets
                    , callableStmts = stmts
                    }
    _ -> Nothing

data DefType = DefTypeBuiltin AS.Identifier
             | DefTypeAbstract AS.Identifier
             | DefTypeAlias AS.Identifier AS.Type
             | DefTypeStruct AS.QualifiedIdentifier [AS.SymbolDecl]
             | DefTypeEnum AS.Identifier [AS.Identifier]
  deriving Show

mkCallableName :: Callable -> T.Text
mkCallableName c =
  let numArgs = length (callableArgs c)
  in mkFunctionName (callableName c) numArgs

asDefType :: AS.Definition -> Maybe DefType
asDefType def =
  case def of
    AS.DefTypeBuiltin ident -> Just $ DefTypeBuiltin ident
    AS.DefTypeAbstract ident -> Just $ DefTypeAbstract ident
    AS.DefTypeAlias ident tp -> Just $ DefTypeAlias ident tp
    AS.DefTypeStruct ident decls -> Just $ DefTypeStruct ident decls
    AS.DefTypeEnum ident idents -> Just $ DefTypeEnum ident idents
    _ -> Nothing

-- | Monad for computing ASL signatures of 'AS.Definition's.
newtype SigM ext f a =
  SigM { _getSigM :: E.ExceptT SigException (RWS.RWST SigEnv () SigState MonadLogIO) a }
  deriving ( Functor
           , Applicative
           , Monad
           , RWS.MonadReader SigEnv
           , RWS.MonadState SigState
           , E.MonadError SigException
           , MonadLog
           )

instance F.MonadFail (SigM ext f) where
  fail s = E.throwError $ SigBindingFailure s

data ASLSpec = ASLSpec
  { aslInstructions :: [AS.Instruction]
  , aslDefinitions :: [AS.Definition]
  , aslSupportDefinitions :: [AS.Definition]
  , aslExtraDefinitions :: [AS.Definition]
  , aslRegisterDefinitions :: [AS.RegisterDefinition]
  }

-- FIXME: One hardcoded register missing from the ASL
extraRegisters :: [AS.RegisterDefinition]
extraRegisters = [
  AS.RegisterDefSingle (AS.Register "TTBCR_S" 32
                       [ mkField "EAE" 31 31
                       , mkField "PD1" 5 5
                       , mkField "PD0" 4 4
                       , mkField "N" 0 2
                       , mkField "SH1" 28 29
                       , mkField "ORGN1" 26 27
                       , mkField "IRGN1" 24 25
                       , mkField "EPD1" 23 23
                       , mkField "T1SZ" 16 18
                       , mkField "SH0" 12 13
                       , mkField "ORGN0" 10 11
                       , mkField "IRGN0" 8 9
                       , mkField "EPD0" 6 6
                       , mkField "T2E" 6 6
                       , mkField "T0SZ" 0 2
                       ])
  ]
  where
    mkField nm lo hi = AS.RegisterField (Just nm) lo hi


prepASL :: ASLSpec -> ASLSpec
prepASL (ASLSpec instrs defs sdefs edefs rdefs) =
  let
    ovrs :: forall t. TR.KnownSyntaxRepr t => t -> t
    ovrs = TR.mkSyntaxOverrides (defs ++ sdefs ++ edefs)
    f = TR.applySyntaxOverridesDefs ovrs
    g = TR.applySyntaxOverridesInstrs ovrs
  in
    ASLSpec (g instrs) (f defs) (f sdefs) (f edefs) (rdefs ++ extraRegisters)


getRegisterType :: AS.Register -> Some WT.BaseTypeRepr
getRegisterType r =
  if | Just (Some wRepr) <- NR.someNat (AS.regLength r)
     , Just NR.LeqProof <- NR.isPosNat wRepr ->
       Some (WT.BaseBVRepr wRepr)
     | otherwise -> error $ "Bad register length: " ++ show (AS.regLength r) ++ " for register " ++ show (AS.regName r)

getRegisterArrayType :: AS.RegisterArray -> Some WT.BaseTypeRepr
getRegisterArrayType ra =
  case getRegisterType (AS.regDef ra) of
    Some t -> Some (WT.BaseArrayRepr (Ctx.empty Ctx.:> WT.BaseIntegerRepr) t)

getRegisterDefType :: AS.RegisterDefinition -> (T.Text, Some WT.BaseTypeRepr)
getRegisterDefType rd = case rd of
  AS.RegisterDefSingle r -> (AS.regName r, getRegisterType r)
  AS.RegisterDefArray ra -> (AS.regName (AS.regDef ra), getRegisterArrayType ra)

getRegisterFieldSlice :: AS.RegisterField -> Maybe (T.Text, (Integer, Integer))
getRegisterFieldSlice rf = case AS.regFieldName rf of
  Just nm -> Just (nm, (AS.regFieldLo rf, AS.regFieldHi rf))
  _ -> Nothing

getRegisterSig :: AS.Register -> RegisterSig
getRegisterSig r =
  Map.fromList $ catMaybes $ map getRegisterFieldSlice (AS.regFields r)

getRegisterDefSig :: AS.RegisterDefinition -> (T.Text, ExtendedTypeData)
getRegisterDefSig rd = case rd of
  AS.RegisterDefSingle r -> (AS.regName r, TypeRegister $ getRegisterSig r)
  AS.RegisterDefArray ra -> (AS.regName (AS.regDef ra), TypeArray $ TypeRegister $ getRegisterSig (AS.regDef ra))

mkCallableOverrideVariant :: Callable -> Callable
mkCallableOverrideVariant Callable{..} =
  Callable nm' callableArgs callableRets callableStmts
  where
    getTypeStr t = case t of
      AS.TypeRef (AS.QualifiedIdentifier _ tpName) -> tpName
      AS.TypeFun "bits" (AS.ExprVarRef (AS.QualifiedIdentifier _ n)) -> "bits" <> n
      _ -> error $ "Bad type for override variant" ++ show t
    nm' = TR.mapInnerName (\nm -> T.concat $ nm : map (\(_, t) -> getTypeStr t) callableArgs) callableName

-- FIXME: This is a gross hack for the fact that the combined support.asl
-- ends up with multiple versions of the same functions
preferLongerCallable :: Callable -> Maybe Callable -> Maybe Callable
preferLongerCallable c1 (Just c2) =
  if (length $ callableStmts c1) > (length $ callableStmts c2)
  then Just c1
  else Just c2
preferLongerCallable c1 Nothing = Just c1

uniqueCallables :: Callable -> Maybe Callable -> Maybe Callable
uniqueCallables c1 (Just _) = error $ "Duplicate function declarations for: " <> (show $ callableName c1)
uniqueCallables c1 Nothing = Just c1


buildCallableMap :: (Callable -> Maybe Callable -> Maybe Callable)
                 -> [(T.Text, Callable)] -> Map.Map T.Text Callable
buildCallableMap merge cs =
  let foo = Map.fromListWith (++) (map (\(nm,c) -> (nm, [c])) cs)
      (overrides, foo') = Map.mapAccumWithKey getOverrides [] foo
      foo'' = Map.mapMaybe id foo' in
  foldr (\c -> Map.alter (merge c) (mkCallableName c)) foo'' overrides

  where
    getOverrides a _ [c] = (a, Just c)
    getOverrides a _ cs' = case nub cs' of
           [c] -> (a, Just c)
           cs'' -> (map mkCallableOverrideVariant cs'' ++ a, Nothing)

mkExtendedTypeData' :: forall m. (Monad m)
                   => (T.Text -> m (Maybe (Some UserType)))
                   -> (T.Text -> m ExtendedTypeData)
                   -> AS.Type
                   -> m ExtendedTypeData
mkExtendedTypeData' getUT getET ty = do
  case ty of
    AS.TypeRef (AS.QualifiedIdentifier _ tident) -> do
      uts <- getUT tident
      case uts of
        Just s -> fromUT s
        Nothing -> do
          case lookup tident registerTypeSynonyms of
            Just nm -> getET nm
            Nothing -> return TypeBasic
    AS.TypeTuple tys -> do
      TypeTuple <$> traverse (mkExtendedTypeData' getUT getET) tys
    _ -> return TypeBasic
  where
    fromUT :: Some UserType -> m ExtendedTypeData
    fromUT ut = case ut of
      Some (UserStruct s) -> do
        asn <- Ctx.traverseAndCollect (collectAssignment (FC.fmapFC projectValue s)) s
        return $ TypeStruct asn
      _ -> return $ TypeBasic
    collectAssignment :: Ctx.Assignment WT.BaseTypeRepr tps
                      -> Ctx.Index tps tp
                      -> LabeledValue (T.Text, Maybe (Some UserType)) WT.BaseTypeRepr tp
                      -> m (Map.Map T.Text StructAccessor)
    collectAssignment repr idx lblv = do
      let (nm, mUT) = projectLabel lblv
      ext <- case mUT of
        Just sUT -> fromUT sUT
        Nothing -> return $ TypeBasic
      return $ Map.singleton nm (StructAccessor repr idx ext)

mkExtendedTypeData :: AS.Type -> SigM ext f (ExtendedTypeData)
mkExtendedTypeData = mkExtendedTypeData' getUT getET
  where
    getUT tpName = Map.lookup tpName <$> userTypes <$> RWS.get
    getET tpName = do
      etd <- RWS.gets extendedTypeData
      return $ fromMaybe TypeBasic (Map.lookup tpName etd)

-- | Given the top-level list of definitions, build a 'SigEnv' for preprocessing the
-- signatures.
buildEnv :: ASLSpec -> SigEnv
buildEnv (spec@ASLSpec{..}) =
  let defs = allDefs spec
      getCallables merge ds = buildCallableMap merge
        ((\c -> (mkCallableName c, c)) <$> (catMaybes (asCallable <$> ds)))

      baseCallables = getCallables uniqueCallables aslDefinitions
      supportCallables = getCallables preferLongerCallable aslSupportDefinitions
      extraCallables = getCallables uniqueCallables aslExtraDefinitions

      -- extras override support callables, which override base callables
      envCallables = Map.union (Map.union extraCallables supportCallables) baseCallables

      types = Map.fromList ((\t -> (getTypeName t, t)) <$> (catMaybes (asDefType <$> defs)))
      -- | TODO: Populate enums
      consts = Map.fromList (builtinConsts ++ catMaybes (getConst <$> defs))
      -- | TODO: Populate builtin types
      builtinTypes = Map.empty
      -- getVariableName v = let DefVariable name _ = v
      --                     in name
      getConst d = case d of
        AS.DefConst name asType e -> case (asType, e) of
          (AS.TypeRef (AS.QualifiedIdentifier _ "integer"), (AS.ExprLitInt i)) ->
            Just (name, Some $ ConstVal WT.BaseIntegerRepr i)
          (AS.TypeFun "bits" (AS.ExprLitInt n), AS.ExprLitBin bv) -> case NR.someNat n of
            Just (Some wRepr) -> case NR.testLeq (NR.knownNat @1) wRepr of
              Just NR.LeqProof ->
                Just (name, Some $ ConstVal (WT.BaseBVRepr wRepr) (BV.mkBV wRepr (bitsToInteger bv)))
              Nothing -> error $ "bv width 0"
            Nothing -> error $ "negative natural " ++ show n
          _ -> Nothing
        _ -> Nothing
      getTypeName t = case t of
        DefTypeBuiltin name -> name
        DefTypeAbstract name -> name
        DefTypeAlias name _ -> name
        DefTypeStruct (AS.QualifiedIdentifier _ name) _ -> name
        DefTypeEnum name _ -> name
  in SigEnv {..}

buildInitState :: ASLSpec -> SigState
buildInitState ASLSpec{..} =
  let globalVars = Map.fromList (map getRegisterDefType aslRegisterDefinitions)
      extendedTypeData = Map.fromList (map getRegisterDefSig aslRegisterDefinitions)
      userTypes = Map.empty
      enums = Map.empty
      callableSignatureMap = Map.empty
      callableOpenSearches = Map.empty
  in SigState{..}

insertUnique :: Ord k => Show k => k -> a -> Map.Map k a -> Map.Map k a
insertUnique k v =
  Map.alter f k
  where
    f x = case x of
      Just _ -> error $ "Unexpected existing member in map:" ++ show k
      Nothing -> Just v

insertNoReplace :: Ord k => Show k => k -> a -> Map.Map k a -> Map.Map k a
insertNoReplace k v =
  Map.alter f k
  where
    f x = case x of
      Just ex -> Just ex
      Nothing -> Just v

globalStructNames :: [T.Text]
globalStructNames = ["PSTATE"]

allDefs :: ASLSpec -> [AS.Definition]
allDefs ASLSpec{..} = aslDefinitions ++ aslSupportDefinitions ++ aslExtraDefinitions


globalFunctions :: [(T.Text, Int)]
globalFunctions =
  [ ("BVMul", 2)
  , ("IntMul", 2)
  , ("IntMod", 2)
  , ("IntDiv", 2)
  , ("setSlice", 4)
  , ("getSlice", 4)
  , ("finishInstruction", 0)
  , ("doAssert", 1)
  ]

initializeSigM :: ASLSpec -> SigM ext f ()
initializeSigM ASLSpec{..} = do

  mapM_ (initDefGlobal insertUnique) aslExtraDefinitions
  mapM_ (initDefGlobal insertNoReplace) aslSupportDefinitions
  mapM_ (initDefGlobal insertNoReplace) aslDefinitions
  mapM_ (uncurry computeGlobalFunctionSig) globalFunctions
  initDefTypes
  where
    computeGlobalFunctionSig :: T.Text -> Int -> SigM ext f ()
    computeGlobalFunctionSig nm nargs = do
      lookupCallable (AS.VarName nm) nargs >>= \case
        Just callable -> void $ computeCallableSignature callable
        _ -> E.throwError $ CallableNotFound nm

    initDefTypes :: SigM ext f ()
    initDefTypes = do
      tps <- RWS.asks types
      mapM_ userTypeOfDef (Map.elems tps)

    initDefGlobal :: (forall k a. Ord k => Show k => k -> a -> Map.Map k a -> Map.Map k a)
                  -> AS.Definition
                  -> SigM ext f ()
    initDefGlobal f (AS.DefVariable (AS.QualifiedIdentifier _ nm) (AS.TypeRef (AS.VarName typnm)))
      | nm `elem` globalStructNames = do
      Some (UserStruct ut) <- computeUserType typnm
      fieldMap <- Ctx.traverseAndCollect (collectGlobalFields nm) ut
      let ext = TypeGlobalStruct fieldMap
      RWS.modify' $ \st -> st { globalVars = f nm (Some (WT.BaseStructRepr Ctx.empty)) (globalVars st),
                     extendedTypeData = f nm ext (extendedTypeData st) }

    initDefGlobal f (AS.DefVariable (AS.QualifiedIdentifier _ nm) ty) = do
      tp <- computeType ty
      ext <- mkExtendedTypeData ty
      st <- RWS.get
      RWS.put $ st { globalVars = f nm tp (globalVars st),
                     extendedTypeData = f nm ext (extendedTypeData st) }
    initDefGlobal f (AS.DefArray nm ty idxty) = do
      Some tp <- computeType ty
      Some idxtp <- computeIdxType idxty
      ext <- mkExtendedTypeData ty
      st <- RWS.get
      let atp = Some $ WT.BaseArrayRepr (Ctx.empty Ctx.:> idxtp) tp
      let aext = TypeArray ext
      RWS.put $ st { globalVars = f nm atp (globalVars st),
                     extendedTypeData = f nm aext (extendedTypeData st) }
    initDefGlobal _ _ = return ()

    collectGlobalFields :: T.Text
                        -> Ctx.Index tps tp
                        -> LabeledValue (T.Text, Maybe (Some UserType)) WT.BaseTypeRepr tp
                        -> SigM ext f (Map.Map T.Text T.Text)
    collectGlobalFields structname _ lblv = do
      let (nm, _) = projectLabel lblv
      let tp = projectValue lblv
      let globalname = structname <> "_" <> nm
      RWS.modify' $ \s -> s { globalVars = insertUnique globalname (Some tp) (globalVars s) }
      return $ Map.singleton nm globalname

computeIdxType :: AS.IndexType -> SigM ext f (Some WT.BaseTypeRepr)
computeIdxType ixt = case ixt of
  AS.IxTypeRange _ _ -> return $ Some WT.BaseIntegerRepr
  AS.IxTypeRef "regidx" -> return $ Some (WT.BaseBVRepr (WT.knownNat @4))
  AS.IxTypeRef "simdidx" -> return $ Some (WT.BaseBVRepr (WT.knownNat @8))
  AS.IxTypeRef nm -> error $ "Unsupported index type: " ++ show nm

buildSigState :: ASLSpec -> LogCfg -> IO (SigEnv, SigState)
buildSigState spec logCfg = do
  let env = (buildEnv spec)
  runSigM (initializeSigM spec) env (buildInitState spec) logCfg  >>= \case
    (Left err, _) -> error $ "Unexpected exception when initializing SigState: " ++ show err
    (Right _, state) -> return (env, state)

runSigM :: SigM ext f a
        -> SigEnv
        -> SigState
        -> LogCfg
        -> IO (Either SigException a, SigState)
runSigM (SigM m) env state logCfg = do
  (result, s, _) <- runMonadLogIO (RWS.runRWST (E.runExceptT m) env state) logCfg
  case result of
    Left err -> return $ (Left err, s)
    Right a -> return $ (Right a, s)

data SigEnv = SigEnv { envCallables :: Map.Map T.Text Callable
                     , consts :: Map.Map T.Text (Some ConstVal)
                     , types :: Map.Map T.Text DefType
                     , builtinTypes :: Map.Map T.Text (Some UserType)
                     }

type GlobalVarRefs = (Set.Set (T.Text, Some WT.BaseTypeRepr), Set.Set (T.Text, Some WT.BaseTypeRepr))

-- All writes are implicitly reads
unpackGVarRefs :: GlobalVarRefs -> ([(T.Text, Some WT.BaseTypeRepr)], [(T.Text, Some WT.BaseTypeRepr)])
unpackGVarRefs (greads, gwrites) =
  let
    globalStructs = Set.fromList $ map (\nm -> (nm, Some (WT.BaseStructRepr Ctx.empty))) globalStructNames
    globalReads = Set.unions [greads, gwrites, builtinReads, builtinWrites] Set.\\ globalStructs
    globalWrites = Set.unions [gwrites, builtinWrites] Set.\\ globalStructs
  in (Set.toList globalReads, Set.toList globalWrites)

builtinReads :: Set.Set (T.Text, Some WT.BaseTypeRepr)
builtinReads = Set.fromList [("__AssertionFailure", Some (WT.knownRepr :: CT.BaseTypeRepr (G.GlobalsType "__AssertionFailure")))]

builtinWrites :: Set.Set (T.Text, Some WT.BaseTypeRepr)
builtinWrites = Set.fromList [("__AssertionFailure", Some (WT.knownRepr :: CT.BaseTypeRepr (G.GlobalsType "__AssertionFailure")))]

-- deriving instance Show (SigEnv ext f)

data SearchStatus = SearchSeen | SearchCollect
  deriving (Eq, Show)

data SigState = SigState { userTypes :: Map.Map T.Text (Some UserType)
                           -- ^ user-defined types
                         , callableSignatureMap :: Map.Map T.Text (SomeSimpleFunctionSignature, Callable, GlobalVarRefs)
                           -- ^ map of all signatures found thus far, including global variable references
                         , callableOpenSearches :: Map.Map T.Text SearchStatus
                           -- ^ all callables encountered on the current search path
                         , enums :: Map.Map T.Text (Some NR.NatRepr, Integer)
                           -- ^ concrete values for enum members
                         , globalVars :: Map.Map T.Text (Some WT.BaseTypeRepr)
                         , extendedTypeData :: Map.Map T.Text ExtendedTypeData
                         }

data SigException = TypeNotFound T.Text
                  | BuiltinTypeNotFound T.Text
                  | CallableNotFound T.Text
                  | VariableNotFound T.Text
                  | WrongType T.Text T.Text
                  | StructMissingField T.Text T.Text
                  | UnsupportedSigExpr AS.Expr
                  | UnsupportedSigStmt AS.Stmt
                  | UnsupportedSigLVal AS.LValExpr
                  | MissingSignature Callable
                  | MissingSigFunctionDefinition T.Text
                  | SigBindingFailure String
                  | FailedToDetermineStaticEnvironment [T.Text]
                  | FailedToMonomorphizeSignature AS.Type StaticValues
                  | UnexpectedRegisterFieldLength T.Text Integer
                  | MissingOrInvalidGlobals [(T.Text, Some WT.BaseTypeRepr)]
                  | MissingGlobals [(T.Text, Some WT.BaseTypeRepr)]
                  | forall tp. InvalidInstructionOperand (T.Text, WT.BaseTypeRepr tp)
                  | InstructionSignatureMismatch [(String, Integer)] [(String, Integer)]
                  | MissingInstructionOperand String

deriving instance Show SigException

storeType :: T.Text -> UserType tp -> SigM ext f ()
storeType tpName tp = do
  st <- RWS.get
  RWS.put $ st { userTypes = Map.insert tpName (Some tp) (userTypes st) }

checkCallableSearch :: Callable -> SigM ext f (Maybe SearchStatus)
checkCallableSearch c = do
  st <- RWS.get
  let name = mkCallableName c
  return $ Map.lookup name (callableOpenSearches st)


setCallableSearch :: Callable -> SearchStatus -> SigM ext f ()
setCallableSearch c stt = do
  st <- RWS.get
  let name = mkCallableName c
  RWS.put $ st { callableOpenSearches =
                 Map.insert name stt (callableOpenSearches st) }

markCallableFound :: Callable -> SigM ext f ()
markCallableFound c = do
  searchStatus <- checkCallableSearch c
  case searchStatus of
    Nothing -> error $ "Unexpected recursive callable call:" ++ show c
    _ -> return ()
  st <- RWS.get
  let name = mkCallableName c
  RWS.put $ st { callableOpenSearches =
                 Map.delete name (callableOpenSearches st) }

lookupCallable :: AS.QualifiedIdentifier -> Int -> SigM ext f (Maybe Callable)
lookupCallable name' arity = do
  env <- RWS.ask
  let name = mkFunctionName name' arity
  return $ Map.lookup name (envCallables env)

lookupBuiltinType :: T.Text -> SigM ext f (Some UserType)
lookupBuiltinType tpName = do
  env <- RWS.ask
  case Map.lookup tpName (builtinTypes env) of
    Just tp -> return tp
    Nothing -> E.throwError $ BuiltinTypeNotFound tpName

lookupDefType :: T.Text -> SigM ext f DefType
lookupDefType tpName = do
  env <- RWS.ask
  case Map.lookup tpName (types env) of
    Just defType -> return defType
    Nothing -> E.throwError $ TypeNotFound tpName

lookupGlobalVar :: T.Text -> SigM ext f (Maybe (Some WT.BaseTypeRepr))
lookupGlobalVar varName = do
  env <- RWS.get
  return $ Map.lookup varName (globalVars env)

lookupExtendedTypeData :: T.Text -> SigM ext f (Maybe ExtendedTypeData)
lookupExtendedTypeData varName = do
  env <- RWS.get
  return $ Map.lookup varName (extendedTypeData env)

lookupCallableSignature :: Callable -> SigM ext f (Maybe (SomeSimpleFunctionSignature, GlobalVarRefs))
lookupCallableSignature c = do
  signatureMap <- callableSignatureMap <$> RWS.get
  let name = mkCallableName c
  case Map.lookup name signatureMap of
    Just (sig, _, globs) -> return $ Just $ (sig, globs)
    _ -> return Nothing

storeCallableSignature :: Callable -> GlobalVarRefs -> SomeSimpleFunctionSignature -> SigM ext f()
storeCallableSignature c gvars sig = do
  st <- RWS.get
  let name = mkCallableName c
  RWS.put $ st { callableSignatureMap = Map.insert name (sig, c, gvars) (callableSignatureMap st) }


-- | If the given type is user-defined, compute its signature and store it
storeUserType :: AS.Type -> SigM ext f ()
storeUserType tp = case applyTypeSynonyms tp of
  AS.TypeRef (AS.QualifiedIdentifier _ tpName) -> do
   case tpName of
     "integer" -> return ()
     "boolean" -> return ()
     "bit" -> return ()
     _ -> do
       _ <- computeUserType tpName
       return ()
  _ -> return ()

userTypeOfDef :: DefType -> SigM ext f (Maybe (Some UserType))
userTypeOfDef defType = do
  case defType of
    DefTypeBuiltin builtinTpName -> Just <$> lookupBuiltinType builtinTpName
    DefTypeEnum _ enumVals
      | nbits <- integerLog2 (fromIntegral (length enumVals)) + 1
      , Just (Some n) <- NR.someNat nbits
      , Just NR.LeqProof <- NR.isPosNat n -> do
      -- Enumeration types are represented as bitvectors.
        forM_ (zip enumVals [0..]) $ \(nm, idx) -> do
          RWS.modify $ \st -> st { enums = Map.insert nm (Some n, idx) (enums st) }
        return $ Just $ Some $ UserEnum n
    DefTypeStruct _ structVars -> do
      varTps <- forM structVars $ \(varName, varType) -> do
        case computeType' varType of
          Left (Some tp) -> do
            return $ Some $ LabeledValue (varName, Nothing) tp
          Right nm -> do
            Some ut <- computeUserType nm
            return $ Some $ LabeledValue (varName, Just (Some ut)) (userTypeRepr ut)
      Some varTpAssignment <- return $ Ctx.fromList varTps
      return $ Just $ Some $ UserStruct varTpAssignment
    _ -> return Nothing

-- | Compute the What4 representation of a user-defined ASL type, from the name of
-- the type as a 'T.Text'. Store it in 'typeSigs' (if it isn't already there).
computeUserType :: T.Text -> SigM ext f (Some UserType)
computeUserType tpName = do
  -- If the type has already been computed, it will be in the 'userTypes' map.
  mTp <- Map.lookup tpName <$> userTypes <$> RWS.get
  case mTp of
    Just tp -> return tp
    Nothing -> do
      -- If it has not already been computed, then compute, store and return it.
      defType <- lookupDefType tpName
      Some tp <- userTypeOfDef defType >>= \case
        Just tp -> return tp
        _ -> error $ "computeUserType: unsupported type " ++ T.unpack tpName
      storeType tpName tp
      return $ Some tp


-- | Either compute the What4 representation of an ASL 'AS.Type' or
-- return a name representing a user-defined type.
computeType' :: AS.Type -> Either (Some WT.BaseTypeRepr) T.Text
computeType' tp = case applyTypeSynonyms tp of
  AS.TypeRef (AS.QualifiedIdentifier _ tpName) -> do
    case tpName of
      "integer" -> Left (Some WT.BaseIntegerRepr)
      "boolean" -> Left (Some WT.BaseBoolRepr)
      "bit" -> Left (Some (WT.BaseBVRepr (NR.knownNat @1)))
      _ -> Right tpName
  AS.TypeFun "bits" e ->
    case e of
      AS.ExprLitInt w
        | Just (Some wRepr) <- NR.someNat w
        , Just NR.LeqProof <- NR.isPosNat wRepr -> Left $ Some (WT.BaseBVRepr wRepr)
      e' -> error $ "computeType, TypeFun" <> show e'
  AS.TypeFun "__RAM" (AS.ExprLitInt n)
    | Just (Some nRepr) <- NR.someNat n
    , Just NR.LeqProof <- NR.isPosNat nRepr ->
      Left $ Some (WT.BaseArrayRepr (Ctx.empty Ctx.:> WT.BaseBVRepr nRepr) (WT.BaseBVRepr (WT.knownNat @8)))
  AS.TypeTuple tps -> let
    ctps = map (\t -> case computeType' t of {Left bt -> bt; _ -> error "Bad type tuple"}) tps
    in case Ctx.fromList ctps of
         Some ctx -> Left $ Some (WT.BaseStructRepr ctx)
  AS.TypeArray tp' (AS.IxTypeRange (AS.ExprLitInt _) (AS.ExprLitInt _)) ->
    case computeType' tp' of
      Left (Some ty) -> Left $ Some $ WT.BaseArrayRepr (Ctx.empty Ctx.:> WT.BaseIntegerRepr) ty
      Right t' -> error $ "invalid target type for array: " ++ show t'

  AS.TypeArray _ _ -> error "computeType, TypeArray"
  AS.TypeOf _ -> error "computeType, TypeOf"
  AS.TypeReg _ _ -> error "computeType, TypeReg"

  _ -> error $ "computeType" ++ show tp

-- | Compute the What4 representation of an ASL 'AS.Type'.
computeType :: AS.Type -> SigM ext f (Some WT.BaseTypeRepr)
computeType tp = case computeType' tp of
  Left ty -> return ty
  Right tpName -> do
    Some userType <- computeUserType tpName
    return $ Some $ userTypeRepr userType

-- | If the identifier is a global variable, return its type. Otherwise, return
-- 'Nothing', indicating the variable is not global.
computeGlobalVarType :: T.Text -> SigM ext f (Maybe (Some WT.BaseTypeRepr))
computeGlobalVarType varName = do
  lookupGlobalVar varName

-- | Given a variable name, determine whether it is a global variable or not. If so,
-- return a pair containing the variable and its type; if not, return 'Nothing'.
varGlobal :: T.Text -> SigM ext f (Maybe (T.Text, Some WT.BaseTypeRepr))
varGlobal varName = do
  mVarType <- computeGlobalVarType varName
  case mVarType of
    Nothing -> return Nothing
    Just varType -> return $ Just (varName, varType)

readGlobal :: T.Text -> SigM ext f GlobalVarRefs
readGlobal varName = do
  greads <- maybeToList <$> varGlobal varName
  return $ (Set.fromList greads, Set.empty)

writeGlobal :: T.Text -> SigM ext f GlobalVarRefs
writeGlobal varName = do
  gwrites <- maybeToList <$> varGlobal varName
  return $ (Set.empty, Set.fromList gwrites)

collectCallables :: Monoid w
                 => (Callable -> [AS.Expr] -> SigM ext f w)
                 -> (AS.QualifiedIdentifier, [AS.Expr])
                 -> SigM ext f w
collectCallables f (AS.QualifiedIdentifier q nm, argEs) =
  mconcat <$> traverse (\(nm',argEs') -> collectCallable (AS.QualifiedIdentifier q nm', argEs')) (overrideFun nm argEs)
  where
    collectCallable (qName, argEs') = do
      mCallable <- lookupCallable qName (length argEs')
      case mCallable of
        Nothing -> return $ mempty
        Just c -> f c argEs


callableGlobalVars :: Callable
                   -> SigM ext f GlobalVarRefs
callableGlobalVars c = do
  msig <- lookupCallableSignature c
  case msig of
    Just (_, globs) -> return globs
    Nothing -> E.throwError $ MissingSignature c

collectStmts :: forall w m
              . Monoid w
             => MonadLog m
             => T.Text
             -> (forall t. TR.KnownSyntaxRepr t => t -> m w)
             -> [AS.Stmt]
             -> m w
collectStmts nm collectors stmts = do
  logMsg 4 ("\nPreprocess: " <> nm)
  mconcat <$> unindentLog (traverse (TR.collectSyntax (TR.collectWithLog 4 collectors)) stmts)


globalsOfStmts :: forall ext f. [AS.Stmt] -> SigM ext f GlobalVarRefs
globalsOfStmts stmts = let
  collectors :: forall t. TR.KnownSyntaxRepr t => t -> SigM ext f GlobalVarRefs
  collectors = TR.useKnownSyntaxRepr $ \syn -> \case
    TR.SyntaxExprRepr -> case syn of
      AS.ExprVarRef (AS.QualifiedIdentifier _ varName) ->
        readGlobal varName
      AS.ExprMember (AS.ExprVarRef (AS.VarName structName)) mem ->
        lookupExtendedTypeData structName >>= \case
          Just (TypeGlobalStruct acc)
            | Just globalName <- Map.lookup mem acc ->
              readGlobal globalName
          _ -> return mempty
      AS.ExprMemberBits e bits ->
        mconcat <$> traverse (TR.collectSyntax collectors) (map (AS.ExprMember e) bits)
      _ -> return mempty
    TR.SyntaxLValRepr -> case syn of
      AS.LValVarRef (AS.QualifiedIdentifier _ varName) ->
        writeGlobal varName
      AS.LValMember (AS.LValVarRef (AS.VarName structName)) mem ->
        lookupExtendedTypeData structName >>= \case
          Just (TypeGlobalStruct acc)
            | Just globalName <- Map.lookup mem acc ->
              writeGlobal globalName
          _ -> return mempty
      AS.LValMemberBits e bits ->
        mconcat <$> traverse (TR.collectSyntax collectors) (map (AS.LValMember e) bits)
      _ -> return mempty
    TR.SyntaxStmtRepr -> case syn of
      AS.StmtCase _ alts ->
        mconcat <$> traverse caseAlternativeGlobalVars alts
      _ -> return mempty
    TR.SyntaxCallRepr -> collectCallables (\c _ -> callableGlobalVars c) syn
    _ -> return mempty
  in collectStmts "globalsOfStmts" collectors stmts
  where
    caseAlternativeGlobalVars alt = case alt of
      AS.CaseWhen pats _ _ -> mconcat <$> traverse casePatternGlobalVars pats
      _ -> return mempty

    casePatternGlobalVars pat = case pat of
      AS.CasePatternIdentifier varName -> readGlobal varName
      AS.CasePatternTuple pats -> mconcat <$> traverse casePatternGlobalVars pats
      _ -> return mempty

directVarsOfExpr :: AS.Expr -> [T.Text]
directVarsOfExpr = \case
  AS.ExprBinOp _ e1 e2 ->
    directVarsOfExpr e1 ++ directVarsOfExpr e2
  AS.ExprVarRef (AS.VarName nm) -> [nm]
  AS.ExprSlice e _ -> directVarsOfExpr e
  AS.ExprCall (AS.VarName "UInt") [e] -> directVarsOfExpr e
  _ -> []


-- | Build a variable dependency graph from the given list of
-- statements
varDepsOfStmts :: Bool
                -- ^ If true, edges go from an lval variable to all rhs variables.
                -- If false, edges go from rhs variables to lvals varibles.
               -> [AS.Stmt]
               -> VarDeps
varDepsOfStmts forward stmts = let
  collectors :: forall t. TR.KnownSyntaxRepr t => t -> I.Identity VarDeps
  collectors = TR.useKnownSyntaxRepr $ \syn -> \case
    TR.SyntaxStmtRepr -> case syn of
      _ | Just _ <- unletInStmt syn ->
          return mempty
      AS.StmtAssign (AS.LValVarRef (AS.VarName lvnm)) e ->
        return $ varDependsExpr lvnm e
      AS.StmtVarDeclInit (lvnm, _) e ->
        return $ varDependsExpr lvnm e
      AS.StmtFor var (lo, hi) _ ->
        return $ varDependsExpr var lo <> varDependsExpr var hi
      _ -> return mempty
    _ -> return mempty
  in I.runIdentity $ collectStmts "varDepsOfStmts" collectors stmts
  where
    varDependsExpr lval e =
      if forward then mconcat $ map (\var -> varDependsOn var lval) $ directVarsOfExpr e
      else mconcat $ map (varDependsOn lval) $ directVarsOfExpr e


computeSignatures :: forall ext f. [AS.Stmt] -> SigM ext f ()
computeSignatures stmts = let
  collectors :: forall t. TR.KnownSyntaxRepr t => t -> SigM ext f ()
  collectors = TR.withKnownSyntaxRepr $ \case
    TR.SyntaxCallRepr -> collectCallables (\c _ -> void $ computeCallableSignature c)
    TR.SyntaxTypeRepr -> storeUserType
    _ -> \_ -> return ()
  in collectStmts "computeSignatures" collectors stmts

-- | For recursive functions, this signature is temporarily stored as a stand-in
-- for the actual function signature when recursively calling the signature
-- calculation.
fakeCallableSignature :: Callable -> SomeSimpleFunctionSignature
fakeCallableSignature c@Callable{..} =
  case (Ctx.fromList [], Ctx.fromList []) of
    (Some globalReadReprs, Some globalWriteReprs) ->
      SomeSimpleFunctionSignature $ SimpleFunctionSignature
      { sfuncName = mkCallableName c
      , sfuncRet = callableRets
      , sfuncArgs = map (\(nm,t) -> FunctionArg nm t) callableArgs
      , sfuncGlobalReadReprs = globalReadReprs
      , sfuncGlobalWriteReprs = globalWriteReprs
      }

-- | Compute the signature of a callable (function/procedure).
computeCallableSignature :: forall ext f. Callable -> SigM ext f (SomeSimpleFunctionSignature, GlobalVarRefs)
computeCallableSignature c@Callable{..} = do
  let name = mkCallableName c
  mSig <- lookupCallableSignature c
  case mSig of
    Just sig -> return sig
    Nothing -> do
      logMsg 4 $ "computeCallableSignature: " <> name
      searchStatus <- checkCallableSearch c
      case searchStatus of
        Nothing -> do
          setCallableSearch c SearchSeen
          computeSignatures callableStmts
          markCallableFound c
          (sig, globalVars) <- getSignature name
          storeCallableSignature c globalVars sig
          return (sig, globalVars)
        Just SearchSeen -> do
          setCallableSearch c SearchCollect
          storeCallableSignature c mempty (fakeCallableSignature c)
          computeSignatures callableStmts
          (sig, globalVars) <- getSignature name
          storeCallableSignature c globalVars sig
          return (sig, globalVars)
        Just SearchCollect -> error $ "Unexpected recursive callable call:" ++ show c

  where
    getLabels vars =
      forM vars $ \(varName, Some varTp) -> do
        return $ Some (LabeledValue varName varTp)
    getSignature name = do
      mapM_ (\(_,t) -> storeUserType t) callableArgs
      mapM_ storeUserType callableRets
      globalVars <- globalsOfStmts callableStmts
      (globalReads, globalWrites) <- return $ unpackGVarRefs $ globalVars
      labeledReads <- getLabels globalReads
      labeledWrites <- getLabels globalWrites
      Some globalReadReprs <- return $ Ctx.fromList labeledReads
      Some globalWriteReprs <- return $ Ctx.fromList labeledWrites

      let sig = SomeSimpleFunctionSignature $ SimpleFunctionSignature
            { sfuncName = name
            , sfuncRet = callableRets
            , sfuncArgs = map (\(nm,t) -> FunctionArg nm t) callableArgs
            , sfuncGlobalReadReprs = globalReadReprs
            , sfuncGlobalWriteReprs = globalWriteReprs
            }
      return (sig, globalVars)


-- Variable dependency tracking
data VarDeps = VarDeps
  { unVarDeps :: Map.Map T.Text (Set.Set T.Text) }
  deriving Show

instance Semigroup VarDeps where
  (VarDeps deps) <> (VarDeps deps') =
    VarDeps (Map.unionWith Set.union deps deps')

instance Monoid VarDeps where
  mempty = VarDeps Map.empty

varDependsOn :: T.Text -> T.Text -> VarDeps
varDependsOn dep var = VarDeps (Map.singleton var (Set.singleton dep))


reachableVarDeps :: VarDeps -> T.Text -> Set.Set T.Text
reachableVarDeps deps var = reachableVarDeps' deps Set.empty (Set.singleton var)
  where
    reachableVarDeps' _ vars frontier = let
      vars' = Set.union vars frontier
      in if vars' == vars
      then vars
      else reachableVarDeps' deps vars' (Set.foldr' addVar Set.empty frontier)
      where
        addVar nm set = case Map.lookup nm (unVarDeps deps) of
          Just set' -> Set.union set set'
          _ -> set

-- FIXME: workaround for the fact that empty tuples are not supported by crucible/what4

mkBaseStructRepr :: [Some WT.BaseTypeRepr] -> Some WT.BaseTypeRepr
mkBaseStructRepr ts = case Ctx.fromList ts of
  Some assignment -> Some (WT.BaseStructRepr assignment)

mkSignature :: StaticValues -> SomeSimpleFunctionSignature -> SigM ext f (Some (SomeFunctionSignature))
mkSignature env sig =
  case sig of
    SomeSimpleFunctionSignature fsig -> do
      Some retTs <- Ctx.fromList <$> mapM mkType (sfuncRet fsig)
      Some args <- Ctx.fromList <$> mapM mkLabel (sfuncArgs fsig)
      return $ Some $ SomeFunctionSignature $ FunctionSignature
        { funcName = mkFinalFunctionName env $ sfuncName fsig
        , funcRetRepr = retTs
        , funcArgReprs = args
        , funcGlobalReadReprs = sfuncGlobalReadReprs fsig
        , funcGlobalWriteReprs = sfuncGlobalWriteReprs fsig
        , funcStaticVals = env
        , funcIsInstruction = False
        }
  where
    mkType t = case applyStaticEnv (simpleStaticEnvMap env) t of
      Just t' -> computeType t'
      _ -> E.throwError $ FailedToMonomorphizeSignature t env
    mkLabel fa@(FunctionArg _ t) = do
      Some tp <- mkType t
      return $ Some (LabeledValue fa tp)

computeFieldType :: AS.InstructionField -> SigM ext f (Some WT.BaseTypeRepr, AS.Type)
computeFieldType AS.InstructionField{..} = do
  case WT.someNat instFieldOffset of
    Nothing -> error $ "Bad field width: " ++ show instFieldName ++ ", " ++ show instFieldOffset
    Just (Some repr) -> case (WT.knownNat @1) `WT.testLeq` repr of
      Nothing -> error $ "Bad field width: " ++ show instFieldName ++ ", " ++ show instFieldOffset
      Just WT.LeqProof -> return $ (Some (WT.BaseBVRepr repr), AS.TypeFun "bin" (AS.ExprLitInt (WT.intValue repr)))


validateEncoding :: DA.Encoding -> SomeInstructionSignature -> SigM ext f ()
validateEncoding daEnc (SomeInstructionSignature iSig) = do
  args <- FC.toListFC (\(Const c) -> c) <$> FC.traverseFC mkSimpleArg (funcArgReprs iSig)
  let ops = DA.encRealOperands daEnc ++ DA.encPseudoOperands daEnc
  unless (args == ops) $ do
    E.throwError $ InstructionSignatureMismatch args ops
  where
    mkSimpleArg :: LabeledValue FunctionArg WT.BaseTypeRepr tp -> SigM ext f (Const (String, Integer) tp)
    mkSimpleArg (LabeledValue (FunctionArg nm _) tr) = case tr of
      WT.BaseBVRepr nr -> return $ Const $ (T.unpack nm, NR.intValue nr)
      _ -> E.throwError $ InvalidInstructionOperand (nm, tr)

finishInstruction :: [AS.Stmt]
finishInstruction = [AS.StmtCall (AS.VarName "finishInstruction") []]

wrapConditionCheck :: Bool -> [AS.Stmt] -> [AS.Stmt]
wrapConditionCheck cond body = case cond of
  True -> [AS.StmtIf [((AS.ExprCall (AS.VarName "ConditionPassed") []), (body ++ finishInstruction))] (Just finishInstruction)]
  False -> body ++ finishInstruction

initGlobals :: [AS.Stmt]
initGlobals = [AS.StmtCall (AS.VarName "initGlobals") []]

-- | Convert an ASL instruction-encoding pair into a function, where the instruction
-- operands are the natural arguments if the resulting function
computeInstructionSignature :: DA.Encoding -- ^ the named constraints that identifies this specific encoding
                            -> AS.Instruction -- ^ ASL instruction
                            -> AS.InstructionEncoding -- ^ ASL encoding
                            -> SigM ext f (SomeInstructionSignature, [AS.Stmt])
computeInstructionSignature daEnc AS.Instruction{..} enc = do
  logMsg 2 $ T.pack $ "computeInstructionSignature: " ++ DA.encName daEnc

  let
    name = T.pack $ DA.encName daEnc
    iset = AS.encInstrSet enc
    initUnusedFields = initializeUnusedFields (AS.encFields enc) (map AS.encFields instEncodings)
    initStmts = initializeEncoding daEnc ++ initInstrEnc iset ++ AS.encDecode enc ++ initGlobals ++ initUnusedFields
  liftedStmts <- liftOverEnvs instName enc instExecute

  let
    instStmts = pruneInfeasableInstrSets iset $
      initStmts
      ++ instPostDecode
      ++ wrapConditionCheck instConditional liftedStmts
    staticEnv = addInitializedVariables initStmts emptyStaticEnvMap
  labeledArgs <- getFunctionArgSig enc daEnc

  computeSignatures instStmts
  globalVars <- globalsOfStmts instStmts

  (globalReads, globalWrites) <- return $ unpackGVarRefs globalVars
  missingGlobals <- liftM catMaybes $ forM globalReads $ \(varName, Some varTp) ->
    case G.lookupGlobal (LabeledValue varName varTp) of
      Just _ -> return Nothing
      Nothing -> return $ Just (varName, Some varTp)
  case missingGlobals of
    [] -> return ()
    _ -> E.throwError $ MissingOrInvalidGlobals missingGlobals

  labeledReads <- forM globalReads $ \(varName, Some varTp) -> do
    return $ Some (LabeledValue varName varTp)
  labeledWrites <- forM globalWrites $ \(varName, Some varTp) -> do
    return $ Some (LabeledValue varName varTp)
  Some globalReadReprs <- return $ Ctx.fromList labeledReads
  Some globalWriteReprs <- return $ Ctx.fromList labeledWrites
  Some argReprs <- return $ Ctx.fromList labeledArgs
  let sig = SomeInstructionSignature $ FunctionSignature { funcName = name
                               , funcArgReprs = argReprs
                               , funcRetRepr = Ctx.empty
                               , funcGlobalReadReprs = globalReadReprs
                               , funcGlobalWriteReprs = globalWriteReprs
                               , funcStaticVals = staticEnvMapVals staticEnv
                               , funcIsInstruction = True
                               }
  validateEncoding daEnc sig
  return (sig, instStmts)

bitMaskToASL :: BM.SomeBitMask BM.QuasiBit -> Either AS.Mask AS.BitVector
bitMaskToASL (BM.SomeBitMask mask) =
  let
    bits = map getMaskBit $ BM.toList mask
  in if all (\(_,mb) -> isJust mb) bits then Right $ map (\(_,mb) -> fromJust mb) bits
  else Left $ map fst bits
  where
    getMaskBit :: BM.QuasiBit -> (AS.MaskBit, Maybe Bool)
    getMaskBit qb = case BM.unQuasiBit qb of
      (BT.ExpectedBit True, _) -> (AS.MaskBitSet, Just True)
      (BT.ExpectedBit False, _) -> (AS.MaskBitUnset, Just False)
      (BT.Any, _) -> (AS.MaskBitEither, Nothing)

initializeEncoding :: DA.Encoding -> [AS.Stmt]
initializeEncoding daEnc =
  map addConstraint (DA.encConstraint daEnc)
  ++ concat (map (map addNegConstraint) (DA.encNegConstraints daEnc))
  where
    nameOf :: DA.FieldConstraint -> AS.QualifiedIdentifier
    nameOf fc = AS.VarName (T.pack $ DA.cFieldName fc)

    addConstraint :: DA.FieldConstraint -> AS.Stmt
    addConstraint fc = case bitMaskToASL (DA.cFieldMask fc) of
      Left mask ->
        AS.StmtAssert (AS.ExprBinOp AS.BinOpEQ (AS.ExprVarRef (nameOf fc)) (AS.ExprLitMask mask))
      Right bv ->
        AS.StmtAssign (AS.LValVarRef (nameOf fc)) (AS.ExprLitBin bv)

    addNegConstraint :: DA.FieldConstraint -> AS.Stmt
    addNegConstraint fc = case bitMaskToASL (DA.cFieldMask fc) of
      Left mask ->
        AS.StmtAssert (AS.ExprBinOp AS.BinOpNEQ (AS.ExprVarRef (nameOf fc)) (AS.ExprLitMask mask))
      Right bv ->
        AS.StmtAssert (AS.ExprBinOp AS.BinOpNEQ (AS.ExprVarRef (nameOf fc)) (AS.ExprLitBin bv))


getFieldsInOrder :: AS.InstructionEncoding -> DA.Encoding -> SigM ext f [AS.InstructionField]
getFieldsInOrder (AS.encFields -> fields) (DA.encRealOperands -> ops) = do
  forM ops $ \(nm, _) -> do
    case find (\field -> AS.instFieldName field == T.pack nm) fields of
      Just field -> return field
      Nothing -> E.throwError $ MissingInstructionOperand nm

getFunctionArgSig :: AS.InstructionEncoding
                  -> DA.Encoding
                  -> SigM ext f [Some (LabeledValue FunctionArg CT.BaseTypeRepr)]
getFunctionArgSig enc daEnc = do
  fields <- getFieldsInOrder enc daEnc
  realops <- forM fields $ \field -> do
    (Some tp, ty) <- computeFieldType field
    let funarg = FunctionArg (AS.instFieldName field) ty
    return (Some (LabeledValue funarg tp))
  pseudoops <- forM (DA.encPseudoOperands daEnc) $ \(nm, w) -> do
    Just (Some nr) <- return $ NR.someNat w
    Just NR.LeqProof <- return $ NR.testLeq (NR.knownNat @1) nr
    let ty = AS.TypeFun "bits" (AS.ExprLitInt w)
    let funarg = FunctionArg (T.pack nm) ty
    return (Some (LabeledValue funarg (WT.BaseBVRepr nr)))
  return $ realops ++ pseudoops

-- | According to the 'dependentVariablesOfStmts', lift the given instruction body
-- over all possible assignments to the given variables in the "decode" section
-- of the specific instruction encoding.
liftOverEnvs :: T.Text -- ^ instruction name (for hint lookup)
             -> AS.InstructionEncoding -- ^ instruction encoding
             -> [AS.Stmt] -- ^ instruction body
             -> SigM ext f [AS.Stmt]
liftOverEnvs instName enc stmts = case dependentVariablesOfStmts stmts of
  ([], _)-> do
    logMsg 2 $ "No dependent variables found for: " <> instName
    return stmts
  (vars', optvars') -> let
    fields = AS.encFields enc
    decodes = AS.encDecode enc
    fieldType (AS.InstructionField instFieldName _ instFieldOffset) =
          (instFieldName, StaticBVType instFieldOffset)
    vartps = map fieldType fields
    decodeVarDeps = varDepsOfStmts True decodes
    decodeVars =
      let
        collectors :: forall t. TR.KnownSyntaxRepr t => t -> I.Identity (Set.Set T.Text)
        collectors = TR.useKnownSyntaxRepr $ \syn -> \case
          TR.SyntaxLValRepr
            | AS.LValVarRef (AS.VarName nm) <- syn ->
              return $ Set.singleton nm
          TR.SyntaxStmtRepr -> case syn of
             AS.StmtVarDeclInit (lvnm, _) _ ->
               return $ Set.singleton lvnm
             AS.StmtVarsDecl _ nms ->
               return $ Set.fromList nms
             _ -> return mempty
          _ -> return mempty
        decodeLVals = I.runIdentity $ mconcat <$> traverse (TR.collectSyntax collectors) decodes
        in decodeLVals
    varDeps = varDepsOfStmts True stmts <> decodeVarDeps

    varsSet = Set.intersection decodeVars (Set.unions $ map (reachableVarDeps varDeps) vars')
    vars = Set.toList varsSet

    optvars = Set.toList $ Set.difference (Set.intersection decodeVars (Set.unions $ map (reachableVarDeps varDeps) optvars')) varsSet

    varToStatic asns var = case Map.lookup var asns of
      Just sv -> (var, sv)
      _ -> error $ "Missing variable in possible assignments: " ++ show var
    optvarToStatic asns optvar = case Map.lookup optvar asns of
      Just sv -> Just (optvar, sv)
      _ -> Nothing
    cases envs = do
      asns <- envs
      let varasns = map (varToStatic asns) vars
      let optvarasns = catMaybes $ map (optvarToStatic asns) optvars
      return $ (varasns ++ optvarasns)
    in do
      logMsg 2 $ "Lifting " <> instName <> " over dependent variables:" <> T.pack (show (vars', optvars'))
      possibleEnvs <- return $ getPossibleVarValues vartps vars optvars decodes
      logMsg 2 $ "Possible environments found: " <> T.pack (show possibleEnvs)
      case cases possibleEnvs of
        [] -> E.throwError $ FailedToDetermineStaticEnvironment vars
        x -> return $ [staticEnvironmentStmt x stmts]

-- | Scan the instruction body for function calls to overly type-dependent functions
dependentVariablesOfStmts :: [AS.Stmt] -> ([T.Text], [T.Text])
dependentVariablesOfStmts stmts = let
  collectors :: forall t. TR.KnownSyntaxRepr t => t -> I.Identity (Set.Set T.Text, Set.Set T.Text)
  collectors = TR.useKnownSyntaxRepr $ \syn -> \case
    TR.SyntaxStmtRepr -> case syn of
      _ | Just _ <- unletInStmt syn -> return mempty
      _ | Just _ <- unblockStmt syn -> return mempty

      AS.StmtAssign (AS.LValVarRef _)
        (AS.ExprSlice (AS.ExprCall (AS.VarName "GETTER_R") _) [AS.SliceRange hi lo]) ->
        return $ directVarsOf hi <> directVarsOf lo
      AS.StmtIf [(e@(AS.ExprVarRef (AS.VarName "floating_point")), _)] _ ->
        return $ directVarsOf e
      AS.StmtFor _ (lo, hi) _ ->
        return $ optionalDirectVarsOf lo <> optionalDirectVarsOf hi
      _ -> return mempty
    TR.SyntaxTypeRepr -> case syn of
      AS.TypeFun "bits" e ->
        return $ directVarsOf e
      _ -> return mempty
    TR.SyntaxCallRepr -> case syn of
      (AS.VarName "GETTER_Elem", [_, e, size]) ->
        return $ optionalDirectVarsOf e <> directVarsOf size
      (AS.VarName "GETTER_Elem", [_, e]) ->
        return $ optionalDirectVarsOf e
      (AS.VarName "SETTER_Elem", [_, _, e, size]) ->
        return $ optionalDirectVarsOf e <> optionalDirectVarsOf size
      (AS.VarName "SETTER_Elem", [_, _, e]) ->
        return $ optionalDirectVarsOf e
      (AS.VarName "GETTER_MemU", [_, size]) ->
        return $ directVarsOf size
      (AS.VarName "SETTER_MemU", [_, _, size]) ->
        return $ directVarsOf size
      (AS.VarName "UnsignedSatQ", [_, saturate_to]) ->
        return $ directVarsOf saturate_to
      (AS.VarName "SignedSatQ", [_, saturate_to]) ->
        return $ directVarsOf saturate_to
      _ -> return mempty
    _ -> return mempty
  (vars, optvars) = I.runIdentity $ mconcat <$> traverse (TR.collectSyntax collectors) stmts
 in (Set.toList vars, Set.toList optvars)
  where
    directVarsOf e = (Set.fromList $ directVarsOfExpr e, Set.empty)
    optionalDirectVarsOf e = (Set.empty, Set.fromList $ directVarsOfExpr e)

-- | Create a copy of the given function body for each given static
-- variable binding environment, prefixing it with the given bindings.
-- Wrap all the copies in an "if" statement that guards for the relevant binding.
staticEnvironmentStmt :: [[(T.Text, StaticValue)]] -- ^ static variable binding environments
                      -> [AS.Stmt] -- ^ instruction body
                      -> AS.Stmt
staticEnvironmentStmt envs stmts =
  AS.StmtIf (map mkCase envs) (Just $ [AS.StmtAssert falseExpr])
  where
    mkCase varasns =
      let
        test = foldr (\asn -> \e ->
          AS.ExprBinOp AS.BinOpLogicalAnd (staticToTest asn) e) trueExpr varasns
        bindings = map staticBinding varasns
      in
        (test, [letInStmt [] (bindings ++ stmts)])
    staticToTest (var, sv) = AS.ExprBinOp AS.BinOpEQ
      (AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny var))
      (SE.staticToExpr sv)

initInstrEnc :: AS.InstructionSet -> [AS.Stmt]
initInstrEnc enc =
  let
    e = case enc of
          AS.A32 -> AS.VarName "__A32"
          AS.T16 -> AS.VarName "__T16"
          AS.T32 -> AS.VarName "__T32"
          AS.A64 -> AS.VarName "__A64"
  in [AS.StmtAssign (AS.LValVarRef (AS.VarName "__ThisInstrEnc")) (AS.ExprVarRef e)]

pruneInfeasableInstrSets :: AS.InstructionSet -> [AS.Stmt] -> [AS.Stmt]
pruneInfeasableInstrSets enc stmts = let
  evalInstrSetTest e = case e of
    AS.ExprBinOp AS.BinOpEQ (AS.ExprCall (AS.VarName "CurrentInstrSet") [])
      (AS.ExprVarRef (AS.VarName "InstrSet_A32")) ->
      case enc of
        AS.A32 -> trueExpr
        _ -> falseExpr
    AS.ExprCall (AS.VarName fpnm) []
      | fpnm `elem` ["HaveFP16MulNoRoundingToFP32Ext", "HaveFP16Ext"] ->
        falseExpr
    _ -> e

  collector :: forall t. TR.KnownSyntaxRepr t => t -> t
  collector = TR.withKnownSyntaxRepr (\case {TR.SyntaxExprRepr -> evalInstrSetTest; _ -> id})
  in map (TR.mapSyntax collector) stmts

-- | In general execution bodies may refer to fields that have not been set by
-- this particular encoding. To account for this, we initialize all fields from
-- other encodings to undefined values, under the assumption that they should not be read.
-- Ambiguous fields (with multiple sizes) are not initialized.
initializeUnusedFields :: [AS.InstructionField] -> [[AS.InstructionField]] -> [AS.Stmt]
initializeUnusedFields encFields allFields =
  let
    getFieldEntry (AS.InstructionField instFieldName _ instFieldOffset) =
      (instFieldName, [instFieldOffset])
    encFieldsSet = Set.fromList (map (\(AS.InstructionField nm _ _) -> nm) encFields)
    fieldsMap = Map.fromListWith (++) (map getFieldEntry $ concat allFields)
    otherFieldsMap = Map.withoutKeys
      fieldsMap
      (Set.insert "cond" encFieldsSet)

    getDecl instFieldName [instFieldOffset] =
        Just $ AS.StmtVarsDecl (AS.TypeFun "bits" (AS.ExprLitInt instFieldOffset)) [instFieldName]
    getDecl _ _ = Nothing
    inits = Map.elems $ Map.mapMaybeWithKey getDecl otherFieldsMap
  in case Set.member "cond" encFieldsSet of
    True -> AS.StmtCall (AS.VarName "setCond") [AS.ExprVarRef $ AS.VarName "cond"] : inits
    False -> inits

-- | Evaluate any known static values for this specific encoding
addInitializedVariables :: [AS.Stmt] -> StaticEnvMap -> StaticEnvMap
addInitializedVariables stmts env =
  foldl addStaticAssignment env stmts
  where
    addStaticAssignment env' stmt = case stmt of
      AS.StmtAssign (AS.LValVarRef (AS.QualifiedIdentifier _ ident)) e
        | Just v <- exprToStatic env' e ->
          insertStaticEnv ident v env'
      AS.StmtVarDeclInit (nm, _) e
        | Just v <- exprToStatic env' e ->
          insertStaticEnv nm v env'
      _ -> env'

-- For a given callable, provide an alternative set of names it might resolve to
-- and optionally an alternative number of arguments it might take.
overrideFun :: T.Text -> [AS.Expr] -> [(T.Text, [AS.Expr])]
overrideFun nm args = case nm of
  "uninterpFnN" -> []
  "uninterpFn" -> []
  "read_mem" -> map (\nm' -> (nm', take 2 args)) $ ["read_mem_1", "read_mem_2", "read_mem_4", "read_mem_8", "read_mem_16"]
  "write_mem" -> map (\nm' -> (nm', take 2 args ++ drop 3 args)) $ ["write_mem_1", "write_mem_2", "write_mem_4", "write_mem_8", "write_mem_16"]
  _ -> map (\nm' -> (nm', args)) $ case nm of
    "__abort" -> ["EndOfInstruction"]
    "TakeHypTrapException" -> ["TakeHypTrapExceptioninteger", "TakeHypTrapExceptionExceptionRecord"]
    _ | nm `elem` ["Min", "Max"] -> [nm <> "integerinteger"]
    "Align" -> ["Alignintegerinteger", "AlignbitsNinteger"]
    _ -> fromMaybe [nm] $
           mkFaultOv nm "IsExternalAbort" <|>
           mkFaultOv nm "IsAsyncAbort" <|>
           mkFaultOv nm "IsSErrorInterrupt" <|>
           mkFaultOv nm "IsExternalSyncAbort"
    where
      mkFaultOv nm' nm'' =
        if nm' == nm''
        then Just $ [nm' <> "FaultRecord", nm' <> "Fault"]
        else Nothing

mkFinalFunctionName :: StaticValues -> T.Text ->  T.Text
mkFinalFunctionName dargs nm = T.concat $ [nm] ++ map (\(nm',i) -> nm' <> "_" <> T.pack (show i)) (Map.assocs dargs)

-- Extra typing hints for local variables, where
-- type inference would otherwise require lookahead
localTypeHints :: Map.Map (T.Text, T.Text) TypeConstraint
localTypeHints = Map.fromList
  [(("AArch32_TranslationTableWalkLD_7", "baseaddress"), ConstraintSingle (CT.BVRepr $ WT.knownNat @40))
  ,(("AArch32_TranslationTableWalkLD_7", "outputaddress"),  ConstraintSingle (CT.BVRepr $ WT.knownNat @40))
  ,(("AArch64_TranslationTableWalk_8", "baseaddress"), ConstraintSingle (CT.BVRepr $ WT.knownNat @52))
  ,(("AArch64_TranslationTableWalk_8", "outputaddress"),  ConstraintSingle (CT.BVRepr $ WT.knownNat @52))
  ]
