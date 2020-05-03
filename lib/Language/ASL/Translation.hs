{-|
Module           : Language.ASL.Translation
Copyright        : (c) Galois, Inc 2019-2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

This is the core module of the ASL translator that defines the
mapping from ASL syntax into Crucible 'Generator' actions. The
ASL syntax is expected to have already been preprocessed with
"Language.ASL.Preprocess" in order to standardize various
syntactic forms, as well as extract the set of global variables
that need to be in scope during translation.
-}

{-# OPTIONS_HADDOCK prune, ignore-exports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.ASL.Translation (
    TranslationState(..)
  , translateBody
  , addExtendedTypeData
  , unliftGenerator
  , Generator
  , InnerGenerator
  , Overrides(..)
  , overrides
  , userTypeRepr
  ) where

import           Control.Lens ( (&), (.~) )
import           Control.Applicative ( (<|>) )
import qualified Control.Exception as X
import           Control.Monad ( when, void, foldM, foldM_, (<=<), forM_, forM )
import qualified Control.Monad.Except as ME
import qualified Control.Monad.Fail as F
import qualified Control.Monad.State.Class as MS
import           Control.Monad.Trans ( lift )
import qualified Control.Monad.Trans as MT
import qualified Control.Monad.State as MSS
import           Control.Monad.Trans.Maybe as MaybeT
import           Data.Typeable
import qualified Data.BitVector.Sized as BV
import           Data.Maybe ( fromMaybe )
import           Data.Void ( Void )
import qualified Data.Void as Void
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Lang.Crucible.CFG.Expr as CCE
import qualified Lang.Crucible.CFG.Generator as CCG
import qualified Lang.Crucible.Types as CT
import qualified What4.BaseTypes as WT
import qualified What4.ProgramLoc as WP
import qualified What4.Utils.StringLiteral as WT
import qualified What4.Concrete as WT

import qualified Language.ASL.Syntax as AS

import           Language.ASL.Crucible.Extension ( ASLExt, ASLApp(..), ASLStmt(..), UFFreshness(..) )
import           Language.ASL.Translation.Exceptions ( TranslationException(..) )
import           Language.ASL.Signature
import           Language.ASL.Types
import           Language.ASL.StaticExpr as SE
import           Language.ASL.Translation.Preprocess
import qualified Language.ASL.SyntaxTraverse as TR
import qualified Language.ASL.SyntaxTraverse as AS ( pattern VarName )
import qualified Language.ASL.Globals as G
import qualified Language.ASL.Globals.Types as G

import qualified Lang.Crucible.CFG.Reg as CCR
import qualified What4.Utils.MonadST as MST
import qualified Data.STRef as STRef

import           What4.Utils.Log ( MonadHasLogCfg(..), LogCfg, logTrace )
import qualified What4.Utils.Log as Log

import           Util.Log ( MonadLog(..), logMsg, logIntToLvl, indentLog, unindentLog )

{- | Translation of ASL into Crucible occurs inside the 'Generator' monad
which wraps the Crucible 'CCG.Generator' with additional error-handling and logging. Functions
can be lifted or unlifted from a 'Generator' to an 'InnerGenerator' via 'liftGenerator' and
'unliftGenerator' respectively.
_-}

-- | A specialization of the Crucible 'CCG.Generator' monad to the ASL 'TranslationState'
type InnerGenerator h s arch ret a =
  CCG.Generator (ASLExt arch) s (TranslationState arch h ret) ret (MST.ST h) a

-- | A wrapped around 'CCG.Generator' with modified error-handling and logging functionality.
newtype Generator h s arch ret a = Generator
  { _unGenerator :: InnerGenerator h s arch ret a}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MSS.MonadState (TranslationState arch h ret s)
    )

-- | Lift an 'InnerGenerator' function to an equivalent 'Generator' function
liftGenerator :: InnerGenerator h s arch ret a
              -> Generator h s arch ret a
liftGenerator m = Generator $ m


-- | Unlift an 'Generator' function to an equivalent 'InnerGenerator' function
unliftGenerator :: Generator h s arch ret a
                -> InnerGenerator h s arch ret a
unliftGenerator (Generator m) = m

throwTrace :: TranslationException -> Generator h s arch ret a
throwTrace e = do
  env <- MSS.gets tsStaticValues
  unindentLog $ logMsg 2 $ "Static Environment: " <> (T.pack (show env))
  X.throw $ e

liftGenerator2 :: Generator h s arch ret a
               -> Generator h s arch ret b
               -> (InnerGenerator h s arch ret a
                  -> InnerGenerator h s arch ret b
                  -> InnerGenerator h s arch ret c)
               -> Generator h s arch ret c
liftGenerator2 (Generator f) (Generator g) m = Generator $ m f g

mkAtom :: CCG.Expr (ASLExt arch) s tp -> Generator h s arch ret (CCG.Atom s tp)
mkAtom e = liftGenerator $ CCG.mkAtom e

instance ME.MonadError TranslationException (Generator h s arch ret) where
  throwError e = throwTrace e
  catchError _handle _m = error "Handle unsupported"

instance MonadHasLogCfg (Generator h s arch ret) where
  getLogCfgM = MSS.gets tsLogCfg

instance MST.MonadST h (Generator h s arch ret) where
  liftST m = Generator $ MT.lift $ MST.liftST m

-- FIXME: replace ST with IO for logging
instance MonadLog (Generator h s arch ret) where
  logMsg logLvl msg = do
    logCfg <- getLogCfgM
    Log.withLogCfg logCfg $ do
      logTrace (logIntToLvl logLvl) (T.unpack msg) `seq` return ()

  logIndent _f = return 0

instance F.MonadFail (Generator h s arch ret) where
  fail s = throwTrace $ BindingFailure s


-- | The internal state of the translator. For the most part this
-- simply retains information about the context of translated function
-- (e.g. in-scope arguments, user type or signatures for other functions).
data TranslationState arch h ret s =
  TranslationState { tsArgAtoms :: Map.Map T.Text (Some (CCG.Atom s))
                   -- ^ Atoms corresponding to function/procedure inputs.  We assume that these are
                   -- immutable and allocated before we start executing.
                   , tsVarRefs :: Map.Map T.Text (Some (CCG.Reg s))
                   -- ^ Local registers containing values; these are created on first use
                   , tsExtendedTypes :: Map.Map T.Text ExtendedTypeData
                   -- ^ Additional type information for local variables
                   , tsGlobals :: Map.Map T.Text (Some CCG.GlobalVar)
                   -- ^ Global variables corresponding to machine state (e.g., machine registers).
                   -- These are allocated before we start executing based on the list of
                   -- transitively-referenced globals in the signature.
                   , tsEnums ::  Map.Map T.Text (Some NR.NatRepr, Integer)
                   -- ^ Map from enumeration constant names to their integer values and bitvector length
                   , tsConsts :: Map.Map T.Text (Some ConstVal)
                   -- ^ Map from constants to their types and values.
                   , tsUserTypes :: Map.Map T.Text (Some UserType)
                   -- ^ The base types assigned to user-defined types (defined in the ASL script)
                   , tsFunctionSigs :: Map.Map T.Text SomeSimpleFunctionSignature
                   -- ^ A collection of all of the signatures of defined functions (both functions
                   -- and procedures)
                   , tsHandle :: STRef.STRef h (Set.Set (T.Text,StaticValues))
                   -- ^ This is used to record any function calls that are made, in order
                   -- to determine additional functions which require translation. The 'StaticValues'
                   -- is the result of unifying the types of the arguments at the call site with
                   -- the signature of the function, concretizing any polymorphic bitvector lengths.
                   , tsStaticValues :: StaticValues
                   -- ^ Environment to give concrete instantiations to polymorphic variables. This
                   -- is mostly populated during initialization, but can be augmented with @constant@
                   -- declarations or in special forms emitted by preprocessing
                   -- (via "Language.ASL.Translation.Preprocess).
                   , tsSig :: SomeFunctionSignature ret
                   -- ^ Signature of the function/procedure we are translating
                   , tsLogCfg :: LogCfg
                   -- ^ logging configuration
                   , tsOverrides :: Overrides arch
                   -- ^ a static collection of syntactic overrides that all expressions and statments
                   -- are checked against before translating
                   }

-- | The top-level translation module which interprets a list of
-- ASL statements ('AS.Stmt') into a sequence of Crucible 'CCG.Generator' actions.
-- In the absence of an explicit @return@ statement, the final statement is assumed
-- to be simply @return;@.
--
-- If the current translation source is an ASL instruction, the "untracked" global
-- variables (from 'G.untrackedGlobals') are initialized with a distinguished
-- uninterpreted function.
translateBody :: forall arch ret h s
               . [AS.Stmt]
              -> Generator h s arch ret ()
translateBody stmts = do
  SomeFunctionSignature sig <- MS.gets tsSig
  FC.forFC_ (funcArgReprs sig) (\(LabeledValue (FunctionArg nm t) _) -> addExtendedTypeData nm t)
  when (funcIsInstruction sig) $ do
    FC.forFC_ (funcGlobalReadReprs sig) initializeUndefinedGlobal
    -- assert that the read globals are in their expected domains.
    -- Currently this is only done at the instruction boundary, where
    -- untracked globals are instantiated to fresh-but-bounded variables.
    preconds <- G.getPrecond GlobalsError lookupGlobalLabel sig
    forM_ preconds $ \(nm, condE) -> do
      condA <- mkAtom condE
      assertAtom condA Nothing $ "Precondition: " <> nm <> " " <> (T.pack $ show condE)
  mapM_ translateStatement stmts
  case funcRetRepr sig of
    Ctx.Empty -> translateStatement (AS.StmtReturn Nothing)
    _ -> return ()

concreteToAtom :: WT.ConcreteVal tp -> Generator h s arch ret (CCG.Atom s (CT.BaseToType tp))
concreteToAtom cv = do
  case cv of
    WT.ConcreteBV nr i -> mkAtom $ CCG.App $ CCE.BVLit nr i
    WT.ConcreteBool b -> mkAtom $ CCG.App $ CCE.BoolLit b
    WT.ConcreteInteger i -> mkAtom $ CCG.App $ CCE.IntLit i
    _ -> throwTrace $ TranslationError $ "unexpected concrete type"

-- | If the given global variable corresponds to an "untracked" global, set its value
-- to be the result of a distinguished nullary uninterpreted function.
initializeUndefinedGlobal :: LabeledValue T.Text WT.BaseTypeRepr tp -> Generator h s arch ret ()
initializeUndefinedGlobal lbl = do
  ts <- MS.get
  case G.lookupGlobal lbl of
    Just (Left gb) -> case Map.lookup (G.gbName gb) (tsGlobals ts) of
      Just (Some gref) | Just Refl <- testEquality (CCG.globalType gref) (CT.baseToType (G.gbType gb)) -> do
        v <- case G.asSingleton (G.gbDomain gb) of
          Just v -> concreteToAtom v
          Nothing -> getInitialGlobal (projectLabel lbl) (projectValue lbl)
        liftGenerator $ CCG.writeGlobal gref (CCG.AtomExpr v)
      _ -> throwTrace $ TranslationError $ "Untracked global missing from registers: " ++ show (G.gbName gb)
    Just (Right _) -> return ()
    Nothing -> throwTrace $ TranslationError $ "No corresponding global with given signature: " ++ show lbl

getInitialGlobal :: forall h s arch ret tp
                 . T.Text
                -> WT.BaseTypeRepr tp
                -> Generator h s arch ret (CCG.Atom s (CT.BaseToType tp))
getInitialGlobal "SIMDS_clone" repr = do
  Some e <- lookupVarRef "SIMDS"
  a <- mkAtom e
  Refl <- assertAtomType' (CT.baseToType repr) a
  return a
getInitialGlobal nm repr = do
  let uf = UF ("INIT_GLOBAL_" <> nm) UFFresh repr Ctx.empty Ctx.empty
  atom <- mkAtom (CCG.App (CCE.ExtensionApp uf))
  return atom

-- * ASL Statement forms

-- | Translate a single ASL statement into Crucible
translateStatement :: forall arch ret h s
                    . AS.Stmt
                   -> Generator h s arch ret ()
translateStatement stmt = do
  logMsg 2 (TR.prettyShallowStmt stmt)
  translateStatement' stmt


translateStatement' :: forall arch ret h s
                    . AS.Stmt
                   -- ^ Statement to be translated
                   -> Generator h s arch ret ()
translateStatement' stmt = do
  ov <- MS.gets tsOverrides
  case overrideStmt ov stmt of
    Just so -> so
    Nothing -> case stmt of
      AS.StmtReturn mexpr -> do
        SomeFunctionSignature sig <- MS.gets tsSig
        -- Natural return type
        let retT = CT.SymbolicStructRepr (funcRetRepr sig)
        let expr = case mexpr of
              Nothing -> AS.ExprTuple []
              Just (AS.ExprTuple es) -> AS.ExprTuple es
              Just e | (Ctx.Empty Ctx.:> _) <- funcRetRepr sig ->
                AS.ExprTuple [e]
              Just e -> e
        (Some a, _) <- translateExpr' expr (ConstraintSingle retT)
        Refl <- assertAtomType expr retT a
        returnWithGlobals a
      AS.StmtIf clauses melse -> translateIf clauses melse
      AS.StmtCase e alts -> translateCase e alts
      AS.StmtAssert e -> assertExpr e "ASL Assertion"
      AS.StmtVarsDecl ty idents -> mapM_ (declareUndefinedVar ty) idents
      AS.StmtVarDeclInit (ident, ty) expr -> translateDefinedVar ty ident expr
      AS.StmtConstDecl (ident, ty) expr -> do
        -- NOTE: We use the same translation for constants.  We don't do any verification that the
        -- ASL doesn't attempt to modify a constant.
        env <- getStaticEnv
        case SE.exprToStatic env expr of
          Just sv -> mapStaticVals (Map.insert ident sv)
          _ -> return ()
        translateDefinedVar ty ident expr

      AS.StmtAssign lval expr -> translateAssignment lval expr
      AS.StmtWhile test body -> do
        let testG = do
              Some testA <- translateExpr test
              Refl <- assertAtomType test CT.BoolRepr testA
              return (CCG.AtomExpr testA)
        let bodyG = indentLog $ mapM_ translateStatement body
        liftGenerator2 testG bodyG $ \testG' bodyG' ->
          CCG.while (WP.InternalPos, testG') (WP.InternalPos, bodyG')
      AS.StmtRepeat body test -> translateRepeat body test
      AS.StmtFor var (lo, hi) body -> translateFor var lo hi body
      AS.StmtCall qIdent args -> do
        translateFunctionCall qIdent args ConstraintNone >>= \case
          Nothing -> return ()
          _ -> throwTrace $ UnexpectedReturnInStmtCall

      _ -> throwTrace $ UnsupportedStmt stmt

finishInstruction :: Generator h s arch ret ()
finishInstruction = void $ translateFunctionCall (AS.VarName "finishInstruction") ([] :: [Void]) ConstraintNone

-- | Translate a @return@ from the current function, combining the
-- current value of all global variables into a struct and returning
-- it with the natural return value of the function.
returnWithGlobals :: ret ~ FuncReturn globalWrites tps
                  => CCG.Atom s (CT.SymbolicStructType tps)
                  -> Generator h s arch ret ()
returnWithGlobals retVal = do
  SomeFunctionSignature sig <- MS.gets tsSig
  when (funcIsInstruction sig) $ do
    -- assert that the write globals are in their expected domains. This is
    -- necessary in order to ensure that our semantics are consistent with respect
    -- to the parts of the global state which are not tracked by our machine model.
    -- e.g. if we assume that the machine is never in debug mode, then we assert
    -- after every instruction that PSTATE_D is always 0.
    postconds <- G.getPostcond GlobalsError lookupGlobalLabel sig
    forM_ postconds $ \(nm, condE) -> do
      condA <- mkAtom condE
      assertAtom condA Nothing $ "Postcondition: " <> nm
    finishInstruction
  returnWithGlobals' retVal

returnWithGlobals' :: ret ~ FuncReturn globalWrites tps
                  => CCG.Atom s (CT.SymbolicStructType tps)
                  -> Generator h s arch ret ()
returnWithGlobals' retVal = do
  let retT = CCG.typeOfAtom retVal
  SomeFunctionSignature sig <- MS.gets tsSig
  withGlobals (funcGlobalWriteReprs sig) $ \globalBaseTypes globals -> liftGenerator $ do
    globalsSnapshot <- CCG.extensionStmt (GetRegState globalBaseTypes globals)
    let result = MkBaseStruct
          (Ctx.empty Ctx.:> CT.SymbolicStructRepr globalBaseTypes Ctx.:> retT)
          (Ctx.empty Ctx.:> globalsSnapshot Ctx.:> CCG.AtomExpr retVal)
    CCG.returnFromFunction (CCG.App $ CCE.ExtensionApp result)

-- | Return from the current function, but with an undefined value
-- as the natural return value.
abnormalExit :: Generator h s arch ret ()
abnormalExit = do
  SomeFunctionSignature sig <- MS.gets tsSig
  let retT = CT.SymbolicStructRepr (funcRetRepr sig)
  defaultv <- getDefaultValue retT
  returnWithGlobals' defaultv

-- | Translate an @if@ statement block into a collection of Crucible
-- if-then-else blocks with 'ifte_'.
translateIf :: [(AS.Expr, [AS.Stmt])]
            -> Maybe [AS.Stmt]
            -> Generator h s arch ret ()
translateIf clauses melse =
  case clauses of
    [] -> indentLog $ mapM_ translateStatement (fromMaybe [] melse)
    (cond, body) : rest ->
      withStaticTest cond
        (mapM_ translateStatement body)
        (translateIf rest melse) $ do
      Some condAtom <- translateExpr cond
      Refl <- assertAtomType cond CT.BoolRepr condAtom
      let genThen = indentLog $ mapM_ translateStatement body
      let genElse = translateIf rest melse
      ifte_ (CCG.AtomExpr condAtom) genThen genElse



-- | Statement-level if-then-else. Newly assigned variables from
-- either branch are implicitly assigned to default
-- values before branching avoid dangling registers.
ifte_ :: CCG.Expr (ASLExt arch) s CT.BoolType
      -> Generator h s arch ret () -- ^ true branch
      -> Generator h s arch ret () -- ^ false branch
      -> Generator h s arch ret ()
ifte_ e (Generator x) (Generator y) = do
  c_id <- liftGenerator $ CCG.newLabel
  (newvarsThen, x_id) <- getNewVars (liftGenerator $ (CCG.defineBlockLabel $ x >> CCG.jump c_id))
  (newvarsElse, y_id) <- getNewVars (liftGenerator $ (CCG.defineBlockLabel $ y >> CCG.jump c_id))
  initVars $ newvarsThen ++ newvarsElse
  liftGenerator $ CCG.continue c_id (CCG.branch e x_id y_id)

getNewVars :: Generator h s arch ret a
           -> Generator h s arch ret ([Some (CCG.Reg s)], a)
getNewVars f = do
  vars <- MS.gets tsVarRefs
  r <- f
  vars' <- MS.gets tsVarRefs
  let diff = Map.difference vars' vars
  return (Map.elems diff, r)

initVars :: [Some (CCG.Reg s)]
         -> Generator h s arch ret ()
initVars regs = do
    mapM_ initVar regs
  where
    initVar (Some reg) = do
      defaultVal <- getDefaultValue (CCG.typeOfReg reg)
      Generator $ CCG.assignReg reg (CCG.AtomExpr defaultVal)

-- | Translate a @case@ statement into a collection of Crucible
-- if-then-else blocks with 'ifte_'.
translateCase :: AS.Expr
              -> [AS.CaseAlternative]
              -> Generator h s arch ret ()
translateCase expr alts = case alts of
  [AS.CaseOtherwise els] -> mapM_ translateStatement els
  -- FIXME: We assume that the case below is equivalent to "otherwise"
  [AS.CaseWhen _ Nothing body] -> mapM_ translateStatement body
  -- FIXME: If we detect an "unreachable", translate it as if the preceding "when"
  -- were "otherwise"
  [AS.CaseWhen _ Nothing body, AS.CaseOtherwise [AS.StmtCall (AS.QualifiedIdentifier _ "Unreachable") []]] ->
    mapM_ translateStatement body
  (AS.CaseWhen pats Nothing body : rst) -> do
    let matchExpr = caseWhenExpr expr pats
    Some matchAtom <- translateExpr matchExpr
    Refl <- assertAtomType matchExpr CT.BoolRepr matchAtom
    let genThen = indentLog $ mapM_ translateStatement body
    let genRest = translateCase expr rst
    ifte_ (CCG.AtomExpr matchAtom) genThen genRest
  _ -> error (show alts)
  where
    caseWhenExpr :: AS.Expr -> [AS.CasePattern] -> AS.Expr
    caseWhenExpr _ [] = error "caseWhenExpr"
    caseWhenExpr expr' [pat] = matchPat expr' pat
    caseWhenExpr expr' (pat:pats) = AS.ExprBinOp AS.BinOpLogicalOr (matchPat expr' pat) (caseWhenExpr expr' pats)

matchPat :: AS.Expr -> AS.CasePattern -> AS.Expr
matchPat expr (AS.CasePatternInt i) = AS.ExprBinOp AS.BinOpEQ expr (AS.ExprLitInt i)
matchPat expr (AS.CasePatternBin bv) = AS.ExprBinOp AS.BinOpEQ expr (AS.ExprLitBin bv)
matchPat expr (AS.CasePatternIdentifier ident) = AS.ExprBinOp AS.BinOpEQ expr (AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny ident))
matchPat expr (AS.CasePatternMask mask) = AS.ExprBinOp AS.BinOpEQ expr (AS.ExprLitMask mask)
matchPat _ AS.CasePatternIgnore = X.throw $ UNIMPLEMENTED "ignore pattern unimplemented"
matchPat _ (AS.CasePatternTuple _) = X.throw $ UNIMPLEMENTED "tuple pattern unimplemented"

-- | Translate a for statement into Crucible
--
-- The translation is from
--
-- > for i = X to Y
-- >    body
--
-- to
--
-- > i = X
-- > while(i <= Y)
-- >   body
-- >   i = i + 1
translateFor :: AS.Identifier
             -> AS.Expr
             -> AS.Expr
             -> [AS.Stmt]
             -> Generator h s arch ret ()
translateFor var lo hi body = do
  env <- getStaticEnv
  case (SE.exprToStatic env lo, SE.exprToStatic env hi) of
    (Just (StaticInt loInt), Just (StaticInt hiInt)) ->
      unrollFor var loInt hiInt body
    _ -> do
      vars <- MS.gets tsVarRefs
      case Map.lookup var vars of
        Just (Some lreg) -> do
          Some atom <- translateExpr lo
          Refl <- assertAtomType' (CCG.typeOfReg lreg) atom
          liftGenerator $ CCG.assignReg lreg (CCG.AtomExpr atom)
        _ -> do
          let ty = AS.TypeRef (AS.QualifiedIdentifier AS.ArchQualAny (T.pack "integer"))
          translateDefinedVar ty var lo
      let ident = AS.QualifiedIdentifier AS.ArchQualAny var
      let testG = do
            let testE = AS.ExprBinOp AS.BinOpLTEQ (AS.ExprVarRef ident) hi
            Some testA <- translateExpr testE
            Refl <- assertAtomType testE CT.BoolRepr testA
            return (CCG.AtomExpr testA)
      let increment = do
            AS.StmtAssign (AS.LValVarRef ident)
              (AS.ExprBinOp AS.BinOpAdd (AS.ExprVarRef ident) (AS.ExprLitInt 1))

      let bodyG = mapM_ translateStatement (body ++ [increment])
      liftGenerator2 testG bodyG $ \testG' bodyG' ->
        CCG.while (WP.InternalPos, testG') (WP.InternalPos, bodyG')

unrollFor :: AS.Identifier
          -> Integer
          -> Integer
          -> [AS.Stmt]
          -> Generator h s arch ret ()
unrollFor var lo hi body = do
  mapM_ translateForUnrolled [lo .. hi]
  where
    translateForUnrolled i = forgetNewStatics $ do
      mapStaticVals (Map.insert var (StaticInt i))
      translateStatement (letInStmt [] body)


-- | Translate a while loop into Crucible
translateRepeat :: [AS.Stmt]
                -> AS.Expr
                -> Generator h s arch ret ()
translateRepeat body test = liftGenerator $ do
  cond_lbl <- CCG.newLabel
  loop_lbl <- CCG.newLabel
  exit_lbl <- CCG.newLabel

  CCG.defineBlock loop_lbl $ do
    unliftGenerator $ mapM_ translateStatement body
    CCG.jump cond_lbl

  CCG.defineBlock cond_lbl $ do
    Some testA <- unliftGenerator $ translateExpr test
    Refl <- unliftGenerator $ assertAtomType test CT.BoolRepr testA
    CCG.branch (CCG.AtomExpr testA) loop_lbl exit_lbl

  CCG.continue exit_lbl (CCG.jump loop_lbl)

-- | Translate an ASL @assert@ statement into a Crucible assertion, as well
-- as tripping the global "Assertion Failure" flag. An explicit @assert FALSE@ is
-- not translated into Crucible, but simply trips the flag.
assertAtom :: CCG.Atom s CT.BoolType
           -> Maybe AS.Expr
           -> T.Text
           -> Generator h s arch ret ()
assertAtom test mexpr msg = do
  case mexpr of
    Just (AS.ExprVarRef (AS.QualifiedIdentifier _ "FALSE")) -> return ()
    Just expr ->
      liftGenerator $ CCG.assertExpr (CCG.AtomExpr test) (CCG.App (CCE.StringLit $ WT.UnicodeLiteral $ msg <> (T.pack $ "Expression: " <> show expr)))
    _ -> liftGenerator $ CCG.assertExpr (CCG.AtomExpr test) (CCG.App (CCE.StringLit $ WT.UnicodeLiteral msg))
  Some assertTrippedE <- lookupVarRef assertionfailureVarName
  assertTripped <- mkAtom assertTrippedE
  Refl <- assertAtomType' CT.BoolRepr assertTripped
  let testFailed = CCG.App $ CCE.Not (CCG.AtomExpr test)
  result <- mkAtom $ CCG.App (CCE.Or (CCG.AtomExpr assertTripped) testFailed)
  translateAssignment' (AS.LValVarRef (AS.QualifiedIdentifier AS.ArchQualAny assertionfailureVarName)) result TypeBasic Nothing

-- * Assignments

-- | Translate general assignment statements into Crucible. The given 'AS.Expr'
-- is translated under any type constraints imposed by the given 'AS.LValExpr' according
-- to 'constraintOfLVal'
translateAssignment :: AS.LValExpr
                    -> AS.Expr
                    -> Generator h s arch ret ()
translateAssignment lval e = do
  -- If possible, determine the type of the left hand side first in order
  -- to inform the translation of the given expression
  constraint <- constraintOfLVal lval
  (Some atom, ext) <- translateExpr' e constraint
  translateAssignment'' lval atom constraint ext (Just e)

-- | Compute a 'TypeConstraint' that the given 'AS.LValExpr' imposes
-- on any expression that would be assigned to it. For example:
--
-- > foo<3:0> = Zeros()
--
-- imposes a constraint that allows @Zeros()@ to be translated into a 4-bit
-- bitvector.
constraintOfLVal :: AS.LValExpr
                 -> Generator h s arch ret TypeConstraint
constraintOfLVal lval = case lval of
  AS.LValIgnore -> return $ ConstraintNone
  AS.LValVarRef (AS.QualifiedIdentifier _ ident) -> do
    mTy <- lookupVarType ident
    case mTy of
      Just (Some ty) -> return $ ConstraintSingle ty
      Nothing -> do
        sig <- MS.gets tsSig
        case Map.lookup (someSigName sig, ident) localTypeHints of
          Just tc -> return $ tc
          _ -> return $ ConstraintNone
  AS.LValTuple lvs -> do
    lvTs <- mapM constraintOfLVal lvs
    return $ ConstraintTuple lvTs
  AS.LValMemberBits _ bits
    | Just (Some nr) <- WT.someNat (length bits)
    , Just WT.LeqProof <- (WT.knownNat @1) `WT.testLeq` nr ->
      return $ ConstraintSingle $ CT.BVRepr nr
  AS.LValSlice lvs -> do
    mTy <- runMaybeT $ do
      lengths <- mapM (bvLengthM <=< lift . constraintOfLVal) lvs
      case WT.someNat (sum lengths) of
        Just (Some repr)
          | Just WT.LeqProof <- (WT.knownNat @1) `WT.testLeq` repr ->
            return $ Some $ CT.BVRepr repr
        _ -> fail ""
    return $ mConstraint mTy
  AS.LValSliceOf e [slice] -> do
    mLen <- getStaticSliceLength slice
    case mLen of
      Just (Some (BVRepr len)) ->
        return $ ConstraintSingle $ CT.BVRepr len
      Nothing -> do
        innerConstraint <- constraintOfLVal e
        return $ relaxConstraint innerConstraint

  _ -> case lValToExpr lval of
         Just lve -> do
           Some lveAtom <- translateExpr lve
           return $ ConstraintSingle $ (CCG.typeOfAtom lveAtom)
         Nothing -> return ConstraintNone
  where
    bvLengthM t = MaybeT (return (bvLength t))

    bvLength :: TypeConstraint -> Maybe Integer
    bvLength tp = case tp of
      ConstraintSingle (CT.BVRepr nr) -> Just (WT.intValue nr)
      _ -> Nothing

    mConstraint :: Maybe (Some (CT.TypeRepr)) -> TypeConstraint
    mConstraint mTy = case mTy of
      Just (Some ty) -> ConstraintSingle ty
      Nothing -> ConstraintNone

translateAssignment' :: forall arch s tp h ret
                      . AS.LValExpr
                     -> CCG.Atom s tp
                     -> ExtendedTypeData
                     -> Maybe AS.Expr
                     -> Generator h s arch ret ()
translateAssignment' lval atom atomext mE =
  translateAssignment'' lval atom (ConstraintSingle (CCG.typeOfAtom atom)) atomext mE

translateAssignment'' :: forall arch s tp h ret
                      . AS.LValExpr
                     -> CCG.Atom s tp
                     -> TypeConstraint
                     -> ExtendedTypeData
                     -> Maybe AS.Expr
                     -> Generator h s arch ret ()
translateAssignment'' lval atom constraint atomext mE = do
  case lval of
    AS.LValIgnore -> return () -- Totally ignore - this probably shouldn't happen (except inside of a tuple)
    AS.LValVarRef (AS.QualifiedIdentifier _ ident) -> do
      isWriteOnly ident >>= \case
        True -> do
          Some curValE <- lookupVarRef ident
          curval <- mkAtom curValE
          Refl <- assertAtomType' (CCG.typeOfAtom curval) atom
          Some isEq <- applyBinOp' eqOp (Nothing, curval) (mE, atom)
          Refl <- assertAtomType' CT.BoolRepr isEq
          assertAtom isEq Nothing ("Assignment to write-only value: " <> T.pack (show lval))
        False -> do
          locals <- MS.gets tsVarRefs
          putExtendedTypeData ident atomext

          case Map.lookup ident locals of
            Just (Some lreg) -> do
              Refl <- assertAtomType' (CCG.typeOfReg lreg) atom
              Generator $ CCG.assignReg lreg (CCG.AtomExpr atom)
            Nothing -> do
              globals <- MS.gets tsGlobals
              case Map.lookup ident globals of
                Just (Some gv) -> do
                  Refl <- assertAtomType' (CCG.globalType gv) atom
                  Generator $ CCG.writeGlobal gv (CCG.AtomExpr atom)
                Nothing -> do
                  reg <- Generator $ CCG.newReg (CCG.AtomExpr atom)
                  MS.modify' $ \s -> s { tsVarRefs = Map.insert ident (Some reg) locals }
    AS.LValMember struct memberName -> do
      Just lve <- return $ lValToExpr struct
      (Some structAtom, ext) <- translateExpr' lve ConstraintNone
      case ext of
        TypeRegister sig ->
          case Map.lookup memberName sig of
            Just slice -> do
              translatelValSlice struct (mkSliceRange slice) atom constraint
            _ -> X.throw $ MissingRegisterField lve memberName
        TypeStruct acc ->
          case (CCG.typeOfAtom structAtom, Map.lookup memberName acc) of
            (CT.SymbolicStructRepr tps, Just (StructAccessor repr idx _))
              | Just Refl <- testEquality tps repr
              , CT.AsBaseType asnBt <- CT.asBaseType $ CCG.typeOfAtom atom
              , Just Refl <- testEquality asnBt (tps Ctx.! idx) -> do
                let ctps = toCrucTypes tps
                let fields = Ctx.generate (Ctx.size ctps) (getStructField tps ctps structAtom)
                let idx' = fromBaseIndex tps ctps idx
                let newStructAsn = fields & (ixF idx') .~ (CCG.AtomExpr atom)
                newStruct <- mkAtom $ CCG.App $ CCE.ExtensionApp $ MkBaseStruct ctps newStructAsn
                translateAssignment' struct newStruct ext Nothing
            _ -> throwTrace $ InvalidStructUpdate lval (CCG.typeOfAtom atom)
        TypeGlobalStruct acc ->
          case Map.lookup memberName acc of
            Just globalName ->
              translateAssignment'' (AS.LValVarRef (AS.QualifiedIdentifier AS.ArchQualAny globalName)) atom constraint atomext mE
            _ -> throwTrace $ MissingGlobalStructField struct memberName

        _ -> throwTrace $ UnexpectedExtendedType lve ext

    AS.LValTuple lvals ->
      case atomext of
        TypeTuple exts | length exts == length lvals ->
          case CCG.typeOfAtom atom of
            CT.SymbolicStructRepr tps -> void $ Ctx.traverseAndCollect (assignTupleElt lvals exts tps atom) tps
            tp -> X.throw $ ExpectedStructType mE tp
        _ -> error $ "Unexpected extended type information:" <> show lvals <> " " <> show atomext

    AS.LValSliceOf lv [slice] -> translatelValSlice lv slice atom constraint

    AS.LValSliceOf lv [fstSlice@(AS.SliceSingle _), slice] -> do
      case CCG.typeOfAtom atom of
        CT.BVRepr wRepr -> do
          let topIndex = WT.intValue wRepr - 1
          Some topBit <- translateSlice' atom (AS.SliceSingle (AS.ExprLitInt topIndex)) ConstraintNone
          translatelValSlice lv fstSlice topBit ConstraintNone
          Some rest <- translateSlice' atom (AS.SliceRange (AS.ExprLitInt (topIndex - 1))
                                                (AS.ExprLitInt 0)) ConstraintNone
          translatelValSlice lv slice rest ConstraintNone
        tp -> throwTrace $ ExpectedBVType' mE tp

    AS.LValArrayIndex ref@(AS.LValVarRef (AS.QualifiedIdentifier _ arrName)) [AS.SliceSingle slice] -> do
        Some e <- lookupVarRef arrName
        arrAtom <- mkAtom e
        Some idxAtom <- translateExpr slice
        if | CT.AsBaseType bt <- CT.asBaseType (CCG.typeOfAtom idxAtom)
           , CT.SymbolicArrayRepr (Ctx.Empty Ctx.:> bt') retTy <- CCG.typeOfAtom arrAtom
           , Just Refl <- testEquality bt bt' -- index types match
           , CT.AsBaseType btAsn <- CT.asBaseType (CCG.typeOfAtom atom)
           , Just Refl <- testEquality btAsn retTy -- array element types match
           -> do
               let asn = Ctx.singleton (CCE.BaseTerm bt (CCG.AtomExpr idxAtom))
               let arr = CCG.App $ CCE.SymArrayUpdate retTy (CCG.AtomExpr arrAtom) asn (CCG.AtomExpr atom)
               newArr <- mkAtom arr
               translateAssignment' ref newArr TypeBasic Nothing
           | otherwise -> error $ "Invalid array assignment: " ++ show lval

    AS.LValArrayIndex _ (_ : _ : _) -> do
      error $
        "Unexpected multi-argument array assignment. Is this actually a setter?" ++ show lval

    AS.LValMemberBits struct bits -> do
      Just lve <- return $ lValToExpr struct
      (Some _, ext) <- translateExpr' lve ConstraintNone
      getRange <- return $ \memberName -> case ext of
        TypeRegister sig ->
          case Map.lookup memberName sig of
            Just (lo, hi) -> return $ (hi - lo) + 1
            _ -> throwTrace $ MissingRegisterField lve memberName
        TypeStruct acc ->
          case Map.lookup memberName acc of
            Just (StructAccessor repr idx _) ->
              case repr Ctx.! idx of
                CT.BaseBVRepr nr -> return $ WT.intValue nr
                x -> throwTrace $ InvalidStructUpdate struct (CT.baseToType x)
            _ -> throwTrace $ MissingStructField lve memberName
        TypeGlobalStruct acc ->
          case Map.lookup memberName acc of
            Just globalname -> do
              lookupVarType globalname >>= \case
                Nothing -> throwTrace $ MissingGlobal globalname
                Just (Some tp) ->
                  case tp of
                    CT.BVRepr nr -> return $ WT.intValue nr
                    x -> throwTrace $ InvalidStructUpdate struct x
            _ -> throwTrace $ MissingGlobalStructField acc memberName
        _ -> throwTrace $ UnexpectedExtendedType lve ext
      total <- foldM (\acc -> \mem -> do
        range <- getRange mem
        Some aslice <- translateSlice' atom (mkSliceRange (acc, (acc + range) - 1)) ConstraintNone
        let lv' = AS.LValMember struct mem
        translateAssignment' lv' aslice TypeBasic Nothing
        return $ acc + range)
        -- FIXME: It's unclear which direction the fields should be read
        0 (List.reverse bits)
      Some (BVRepr trepr) <- return $ intToBVRepr total
      _ <- assertAtomType' (CT.BVRepr trepr) atom
      return ()

    AS.LValSlice lvs ->
      case CCG.typeOfAtom atom of
        CT.BVRepr repr -> foldM_ (translateImplicitSlice repr atom) 0 lvs
        tp -> throwTrace $ ExpectedBVType' mE tp

    _ -> X.throw $ UnsupportedLVal lval
    where assignTupleElt :: [AS.LValExpr]
                         -> [ExtendedTypeData]
                         -> Ctx.Assignment WT.BaseTypeRepr ctx
                         -> CCG.Atom s (CT.SymbolicStructType ctx)
                         -> Ctx.Index ctx tp'
                         -> WT.BaseTypeRepr tp'
                         -> Generator h s arch ret ()
          assignTupleElt lvals exts tps struct ix _ = do
            let getStruct = GetBaseStruct (CT.SymbolicStructRepr tps) ix (CCG.AtomExpr struct)
            getAtom <- mkAtom (CCG.App (CCE.ExtensionApp getStruct))
            let ixv = Ctx.indexVal ix
            translateAssignment' (lvals !! ixv) getAtom (exts !! ixv) Nothing

          getStructField :: forall bctx ctx ftp
                          . ctx ~ ToCrucTypes bctx
                         => Ctx.Assignment CT.BaseTypeRepr bctx
                         -> Ctx.Assignment CT.TypeRepr ctx
                         -> CCG.Atom s (CT.SymbolicStructType bctx)
                         -> Ctx.Index ctx ftp
                         -> CCG.Expr (ASLExt arch) s ftp
          getStructField btps ctps struct ix = case toFromBaseProof (ctps Ctx.! ix) of
            Just Refl ->
              let
                  ix' = toBaseIndex btps ctps ix
                  getStruct =
                    (GetBaseStruct (CT.SymbolicStructRepr btps) ix' (CCG.AtomExpr struct)) ::
                      ASLApp (CCG.Expr (ASLExt arch) s) ftp
              in
                CCG.App $ CCE.ExtensionApp getStruct
            _ -> error "unreachable"

          isWriteOnly :: T.Text -> Generator h s arch ret Bool
          isWriteOnly name = do
            ts <- MS.get
            env <- getStaticEnv
            return $

              -- FIXME: In "InstructionDevice" we see a struct that is modified in-place, but returned.
              -- Violating that args are write-only, but also causing a translation failure since
              -- we can't assert equality of structs
              --   Map.member name (tsArgAtoms ts)
                 Map.member name (tsEnums ts)
              || Map.member name (tsConsts ts)
              || isJust (staticEnvValue env name)

-- | Translate the declaration of a new variable into Crucible by initializing a
-- fresh register.
translateDefinedVar :: AS.Type
                    -> AS.Identifier
                    -> AS.Expr
                    -> Generator h s arch ret ()
translateDefinedVar ty ident expr = do
  Some expected <- translateType ty
  (Some atom, ext) <- translateExpr' expr (ConstraintSingle expected)
  Refl <- assertAtomType expr expected atom
  locals <- MS.gets tsVarRefs
  when (Map.member ident locals) $ do
    X.throw (LocalAlreadyDefined ident)
  putExtendedTypeData ident ext
  reg <- Generator $ CCG.newReg (CCG.AtomExpr atom)
  MS.modify' $ \s -> s { tsVarRefs = Map.insert ident (Some reg) locals }

-- | Put a new local in scope and initialize it to an undefined value
declareUndefinedVar :: AS.Type
                    -> AS.Identifier
                    -> Generator h s arch ret ()
declareUndefinedVar ty ident = do
  ts <- MS.get
  lookupVarRef' ident >>= \case
    Just _ -> throwTrace $ LocalAlreadyDefined ident
    Nothing -> return ()
  addExtendedTypeData ident ty
  tty <- translateType ty
  case tty of
    Some rep -> do
      defaultv <- getDefaultValue rep
      reg <- Generator $ CCG.newReg (CCG.AtomExpr defaultv)
      MS.modify' $ \s -> s { tsVarRefs = Map.insert ident (Some reg) (tsVarRefs ts) }

-- | Translate a sliced bitvector assignment. e.g. @bv<i:j> = val@
translatelValSlice :: AS.LValExpr
                   -- ^ the sliced bitvector. e.g. @bv@
                   -> AS.Slice
                   -- ^ the slice of the bitvector. e.g. @<i:j>@
                   -> CCG.Atom s tp
                   -- ^ the value being assigned to the slice
                   -> TypeConstraint
                   -- ^ any known constraints determining the size of the slice
                   -> Generator h s arch ret ()
translatelValSlice lv slice asnAtom' constraint = do
  let Just lve = lValToExpr lv
  Some atom' <- translateExpr lve
  SliceRange signed lenRepr _ loAtom hiAtom atom <- getSliceRange slice atom' constraint
  asnAtom <- extBVAtom signed lenRepr asnAtom'
  Just (Some result, _) <- translateFunctionCall (AS.VarName "setSlice") [Some atom, Some loAtom, Some hiAtom, Some asnAtom] ConstraintNone
  translateAssignment' lv result TypeBasic Nothing

-- | Translate an assignment to a bitvector slice, where the width is implicit
-- based on the variable being assigned to. e.g. given @PSTATE.<N,Z,C,V> = var@
-- we translate a series of assignments:
--
-- > PSTATE.N = var<3>;
-- > PSTATE.Z = var<2>;
-- > PSTATE.C = var<1>;
-- > PSTATE.V = var<0>;
translateImplicitSlice :: WT.NatRepr w
                       -- ^ the width of the atom being sliced
                       -> CCG.Atom s (CT.BVType w)
                       -- ^ the source atom of the slice. e.g. @var@
                       -> Integer
                       -- ^ the variable index of this slice. e.g. @1@
                       -> AS.LValExpr
                       -- ^ the specific l-value that this assignment is to. e.g. @PSTATE.C@
                       -> Generator h s arch ret (Integer)
translateImplicitSlice rhsRepr rhs offset lv  = do
  lvT <- constraintOfLVal lv
  case lvT of
    ConstraintSingle (CT.BVRepr lvRepr) -> do
      let lvLength = WT.intValue lvRepr
      let rhsLength = WT.intValue rhsRepr
      let hi = rhsLength - offset - 1
      let lo = rhsLength - offset - lvLength
      let slice = AS.SliceRange (AS.ExprLitInt hi) (AS.ExprLitInt lo)
      Some slicedRhs <- translateSlice' rhs slice ConstraintNone
      translateAssignment' lv slicedRhs TypeBasic Nothing
      return (offset + lvLength)
    _ -> X.throw $ UnsupportedLVal lv

-- * Expressions

-- | Translate an ASL expression into an Atom (which is a reference to an immutable value)
--
-- Atoms may be written to registers, which are mutable locals
translateExpr :: AS.Expr
              -> Generator h s arch ret (Some (CCG.Atom s))
translateExpr expr = do
  (atom, _) <- translateExpr' expr ConstraintNone
  return atom

translateExpr' :: AS.Expr
              -> TypeConstraint
              -> Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData)
translateExpr' expr constraint = do
  logMsg 2 $ T.pack (show expr) <> " :: " <> T.pack (show constraint)
  translateExpr'' expr constraint

translateExpr'' :: AS.Expr
              -> TypeConstraint
              -> Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData)
translateExpr'' expr ty = do
  env <- getStaticEnv
  ov <- MS.gets tsOverrides
  case overrideExpr ov expr ty env of
    Just f -> f
    Nothing -> do
      mStatic <- getStaticValue expr
      case mStatic of
        Just (StaticInt i) -> mkAtom' (CCG.App (CCE.IntLit i))
        Just (StaticBool b) -> mkAtom' (CCG.App (CCE.BoolLit b))
        _ -> case expr of
          AS.ExprLitInt i -> mkAtom' (CCG.App (CCE.IntLit i))
          AS.ExprLitBin bits
            | Some bvexpr <- bitsToBVExpr bits ->
              mkAtom' bvexpr

          AS.ExprVarRef (AS.QualifiedIdentifier _ ident) -> do
            Some e <- lookupVarRef ident
            atom <- mkAtom e
            ext <- getExtendedTypeData ident
            return (Some atom, ext)

          AS.ExprLitReal {} -> throwTrace $ UnsupportedExpr expr
          AS.ExprLitString {} -> throwTrace $ UnsupportedExpr expr
          AS.ExprUnOp op expr' -> basicExpr $ translateUnaryOp op expr'
          AS.ExprBinOp op e1 e2 -> basicExpr $ translateBinaryOp op e1 e2 ty
          AS.ExprTuple exprs -> do
            atomExts <- case ty of
              ConstraintSingle (CT.SymbolicStructRepr tps) -> do
                let exprTs = zip (FC.toListFC Some tps) exprs
                mapM (\(Some ty', e) -> translateExpr' e (ConstraintSingle (CT.baseToType ty'))) exprTs
              ConstraintTuple cts -> do
                mapM (\(ct, e) -> translateExpr' e ct) (zip cts exprs)
              _ -> do
               mapM (\e -> translateExpr' e ConstraintNone) exprs
            let (atoms, exts) = unzip atomExts
            case Ctx.fromList atoms of
              Some asgn -> do
                let reprs = FC.fmapFC CCG.typeOfAtom asgn
                let atomExprs = FC.fmapFC CCG.AtomExpr asgn
                let struct = MkBaseStruct reprs atomExprs
                atom <- mkAtom (CCG.App (CCE.ExtensionApp struct))
                return (Some atom, TypeTuple exts)

          AS.ExprInSet e elts -> do
            Some atom <- translateExpr e
            when (null elts) $ X.throw (EmptySetElementList expr)
            preds <- mapM (translateSetElementTest expr atom) elts
            mkAtom' (foldr disjoin (CCG.App (CCE.BoolLit False)) preds)
          AS.ExprIf clauses elseExpr -> translateIfExpr expr clauses elseExpr ty

          AS.ExprCall qIdent args -> do
            ret <- translateFunctionCall qIdent args ty
            case ret of
              Just x -> return x
              Nothing -> throwTrace $ UnexpectedReturnInExprCall
          -- FIXME: Should this trip a global flag?
          AS.ExprImpDef _ t -> do
            Some ty' <- translateType t
            defaultv <- getDefaultValue ty'
            return (Some defaultv, TypeBasic)

          AS.ExprMember struct memberName -> do
            (Some structAtom, ext) <- translateExpr' struct ConstraintNone
            case ext of
              TypeRegister sig -> do
                case Map.lookup memberName sig of
                  Just slice -> do
                    satom <- translateSlice struct (mkSliceRange slice) ConstraintNone
                    return (satom, TypeBasic)
                  _ -> X.throw $ MissingRegisterField struct memberName
              TypeStruct acc -> do
                case (CCG.typeOfAtom structAtom, Map.lookup memberName acc) of
                  (CT.SymbolicStructRepr tps, Just (StructAccessor repr idx fieldExt)) |
                    Just Refl <- testEquality tps repr -> do
                      let getStruct = GetBaseStruct (CT.SymbolicStructRepr tps) idx (CCG.AtomExpr structAtom)
                      atom <- mkAtom (CCG.App (CCE.ExtensionApp getStruct))
                      return (Some atom, fieldExt)
                  _ -> throwTrace $ MissingStructField struct memberName
              TypeGlobalStruct acc ->
                case Map.lookup memberName acc of
                  Just globalName -> do
                    translateExpr' (AS.ExprVarRef (AS.QualifiedIdentifier AS.ArchQualAny globalName)) ty
                  _ -> throwTrace $ MissingGlobalStructField struct memberName
              _ -> X.throw $ UnexpectedExtendedType struct ext

          AS.ExprMemberBits var bits -> do
            let (hdvar : tlvars) = map (\member -> AS.ExprMember var member) bits
            let expr' = foldl (\var' -> \e -> AS.ExprBinOp AS.BinOpConcat var' e) hdvar tlvars
            translateExpr' expr' ty

          AS.ExprSlice e [slice] -> do
            satom <- translateSlice e slice ty
            return (satom, TypeBasic)

          AS.ExprSlice e (slice : slices) -> do
            let expr' = AS.ExprBinOp AS.BinOpConcat (AS.ExprSlice e [slice]) (AS.ExprSlice e slices)
            translateExpr' expr' ty

          AS.ExprIndex array [AS.SliceSingle slice]  -> do
            (Some atom, ext) <- translateExpr' array ConstraintNone
            Some idxAtom <- translateExpr slice
            if | CT.AsBaseType bt <- CT.asBaseType (CCG.typeOfAtom idxAtom)
               , CT.SymbolicArrayRepr (Ctx.Empty Ctx.:> bt') retTy <- CCG.typeOfAtom atom
               , Just Refl <- testEquality bt bt' -> do
                   let asn = Ctx.singleton (CCE.BaseTerm bt (CCG.AtomExpr idxAtom))
                   let arr = CCE.SymArrayLookup retTy (CCG.AtomExpr atom) asn
                   ext' <- case ext of
                     TypeArray ext' -> return ext'
                     _ -> return TypeBasic
                   atom' <- mkAtom (CCG.App arr)
                   return (Some atom', ext')
               | otherwise -> throwTrace $ UnsupportedExpr expr
          AS.ExprUnknown t -> do
            Some ty' <- translateType t
            defaultv <- getDefaultValue ty'
            return (Some defaultv, TypeBasic)

          _ -> throwTrace $ UnsupportedExpr expr
  where
    basicExpr f = do
      satom <- f
      return (satom, TypeBasic)

-- | Get the "default" value for a given crucible type. We can't use unassigned
-- registers, as ASL functions occasionally return values uninitialized.
getDefaultValue :: forall h s arch ret tp
                 . CT.TypeRepr tp
                -> Generator h s arch ret (CCG.Atom s tp)
getDefaultValue repr = case repr of
  CT.BVRepr nr -> mkUF ("UNDEFINED_bitvector_" <> T.pack (show (WT.intValue nr))) repr
  CT.SymbolicStructRepr tps -> do
    let crucAsn = toCrucTypes tps
    if | Refl <- baseCrucProof tps -> do
         fields <- FC.traverseFC getDefaultValue crucAsn
         mkAtom $ CCG.App $ CCE.ExtensionApp $
           MkBaseStruct crucAsn (FC.fmapFC CCG.AtomExpr fields)
  CT.IntegerRepr -> mkUF "UNDEFINED_integer" repr
  CT.BoolRepr -> mkUF "UNDEFINED_boolean" repr
  -- CT.SymbolicArrayRepr (Ctx.Empty Ctx.:> WT.BaseIntegerRepr) (WT.BaseBVRepr _)
  --  -> mkUF "UNDEFINED_IntArray" repr
  _ -> error $ "Invalid undefined value: " <> show repr

-- ** Slicing Expressions

-- | Translate a bitvector slice expression into a crucible 'CCG.Atom'.
translateSlice :: AS.Expr
               -> AS.Slice
               -> TypeConstraint
               -> Generator h s arch ret (Some (CCG.Atom s))
translateSlice e slice constraint = do
   Some atom <- translateExpr e
   translateSlice' atom slice constraint

translateSlice' :: CCG.Atom s tp
                -> AS.Slice
                -> TypeConstraint
                -> Generator h s arch ret (Some (CCG.Atom s))
translateSlice' atom' slice constraint = do
  SliceRange signed lenRepr wRepr loAtom hiAtom atom <- getSliceRange slice atom' constraint
  case lenRepr `WT.testNatCases` wRepr of
    WT.NatCaseEQ ->
      -- when the slice covers the whole range we just return the whole atom
      return $ Some $ atom
    WT.NatCaseLT WT.LeqProof -> do
      signedAtom <- mkAtom $ CCG.App $ CCE.BoolLit signed
      Just (sresult, _) <- translateFunctionCall (AS.VarName "getSlice")
        [Some atom, Some signedAtom, Some loAtom, Some hiAtom] (ConstraintSingle (CT.BVRepr lenRepr))
      return sresult
    _ -> throwTrace $ UnsupportedSlice slice constraint

normalizeSlice :: AS.Slice -> (AS.Expr, AS.Expr)
normalizeSlice slice = case slice of
  AS.SliceRange e e' -> (e', e)
  AS.SliceSingle e -> (e, e)
  AS.SliceOffset e e' ->
    let hi = AS.ExprBinOp AS.BinOpAdd e (AS.ExprBinOp AS.BinOpSub e' (AS.ExprLitInt 1))
        in (e, hi)

data SliceRange s where
  SliceRange :: (1 WT.<= atomLength, 1 WT.<= sliceLength, sliceLength WT.<= atomLength)
                => Bool -- requires signed extension
                -> WT.NatRepr sliceLength
                -> WT.NatRepr atomLength
                -> CCG.Atom s CT.IntegerType
                -> CCG.Atom s CT.IntegerType
                -> CCG.Atom s (CT.BVType atomLength)
                -> SliceRange s

exprRangeToLength :: StaticEnvMap -> AS.Expr -> AS.Expr -> Maybe Integer
exprRangeToLength env lo hi = case (lo, hi) of
  (AS.ExprVarRef loVar, AS.ExprBinOp AS.BinOpAdd e (AS.ExprVarRef hiVar)) -> getStaticLength loVar hiVar e
  (AS.ExprVarRef loVar, AS.ExprBinOp AS.BinOpAdd (AS.ExprVarRef hiVar) e) -> getStaticLength loVar hiVar e
  (AS.ExprBinOp AS.BinOpSub (AS.ExprVarRef loVar) e, AS.ExprVarRef hiVar) -> getStaticLength loVar hiVar e
  (e, e') | e == e' -> Just 1
  _ | Just (StaticInt loInt) <- SE.exprToStatic env lo
    , Just (StaticInt hiInt) <- SE.exprToStatic env hi ->
      Just $ (hiInt - loInt) + 1
  _ -> Nothing

  where getStaticLength loVar hiVar e =
          if | loVar == hiVar
             , Just (StaticInt i) <- SE.exprToStatic env e
             , i > 0 ->
               Just $ i + 1
             | otherwise -> Nothing

getStaticSliceLength :: AS.Slice
                     -> Generator h s arch ret (Maybe (Some BVRepr))
getStaticSliceLength slice = do
  let (e', e) = normalizeSlice slice
  env <- getStaticEnv
  if | Just len <- exprRangeToLength env e' e
     , Just (Some lenRepr) <- WT.someNat len
     , Just WT.LeqProof <- (WT.knownNat @1) `WT.testLeq` lenRepr ->
        return $ Just $ Some $ BVRepr lenRepr
     | otherwise -> return Nothing

getSymbolicSliceRange :: AS.Slice
                      -> Generator h s arch ret (CCG.Atom s CT.IntegerType, CCG.Atom s CT.IntegerType)
getSymbolicSliceRange slice = do
  let (e', e) = normalizeSlice slice
  Some loAtom <- translateExpr e'
  Some hiAtom <- translateExpr e
  Refl <- assertAtomType e' CT.IntegerRepr loAtom
  Refl <- assertAtomType e CT.IntegerRepr hiAtom
  return (loAtom, hiAtom)

getSliceRange :: AS.Slice
              -> CCG.Atom s tp
              -> TypeConstraint
              -> Generator h s arch ret (SliceRange s)
getSliceRange slice slicedAtom constraint = do
  (loAtom, hiAtom) <- getSymbolicSliceRange slice
  mLength <- getStaticSliceLength slice
  (Some lenRepr :: Some WT.NatRepr, signed :: Bool) <- case mLength of
    Just (Some (BVRepr len)) -> return $ (Some len, False)
    _ -> case constraint of
      ConstraintSingle (CT.BVRepr len) -> return $ (Some len, False)
      ConstraintHint (HintMaxBVSize maxlength) ->
        case CCG.typeOfAtom slicedAtom of
          CT.BVRepr wRepr -> case wRepr `WT.testNatCases` maxlength of
            WT.NatCaseEQ -> return $ (Some wRepr, False)
            WT.NatCaseLT _ -> return $ (Some wRepr, False)
            WT.NatCaseGT WT.LeqProof -> return $ (Some maxlength, False)
          CT.IntegerRepr -> return $ (Some maxlength, False)
          _ -> throwTrace $ UnsupportedSlice slice constraint
      ConstraintHint (HintMaxSignedBVSize maxlength) ->
        case CCG.typeOfAtom slicedAtom of
          CT.BVRepr wRepr -> case wRepr `WT.testNatCases` maxlength of
            WT.NatCaseEQ -> return $ (Some wRepr, False)
            WT.NatCaseLT _ -> return $ (Some wRepr, False)
            WT.NatCaseGT WT.LeqProof -> return $ (Some maxlength, True)
          CT.IntegerRepr -> return $ (Some maxlength, True)
          _ -> throwTrace $ UnsupportedSlice slice constraint
      ConstraintHint HintAnyBVSize ->
        case CCG.typeOfAtom slicedAtom of
          CT.BVRepr wRepr -> return $ (Some wRepr, False)
          _ -> throwTrace $ UnsupportedSlice slice constraint
      _ -> throwTrace $ UnsupportedSlice slice constraint
  WT.LeqProof <- case (WT.knownNat @1) `WT.testLeq` lenRepr of
    Just x -> return x
    _ -> throwTrace $ UnsupportedSlice slice constraint
  case CCG.typeOfAtom slicedAtom of
    CT.BVRepr wRepr
      | Just WT.LeqProof <- lenRepr `WT.testLeq` wRepr ->
        return $ SliceRange signed lenRepr wRepr loAtom hiAtom slicedAtom
    CT.IntegerRepr -> do
      env <- getStaticEnv
      let (_, hi) = normalizeSlice slice
      case SE.exprToStatic env hi of
        Just (StaticInt hi') | Some (BVRepr hiRepr) <- intToBVRepr (hi'+1) ->
            if | Just WT.LeqProof <- lenRepr `WT.testLeq` hiRepr -> do
                 intAtom <- mkAtom $ integerToSBV hiRepr (CCG.AtomExpr slicedAtom)
                 return $ SliceRange signed lenRepr hiRepr loAtom hiAtom intAtom
               | otherwise -> throwTrace $ InvalidSymbolicSlice lenRepr hiRepr
        _ -> throwTrace $ RequiredConcreteValue hi (staticEnvMapVals env)
    _ -> throwTrace $ UnsupportedSlice slice constraint

-- ** Conditionals

-- | Translate the expression form of a conditional into a Crucible atom
translateIfExpr :: AS.Expr
                -> [(AS.Expr, AS.Expr)]
                -> AS.Expr
                -> TypeConstraint
                -> Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData)
translateIfExpr orig clauses elseExpr ty =
  case clauses of
    [] -> X.throw (MalformedConditionalExpression orig)
    [(test, res)] ->
      withStaticTest test
        (translateExpr' res ty)
        (translateExpr' elseExpr ty) $ do
      Some testA <- translateExpr test
      (Some resA, extRes) <- translateExpr' res ty
      (Some elseA, extElse) <- translateExpr' elseExpr (mergeConstraints ty (someTypeOfAtom resA))
      ext <- mergeExtensions extRes extElse
      Refl <- assertAtomType test CT.BoolRepr testA
      Refl <- assertAtomType res (CCG.typeOfAtom elseA) resA
      case CT.asBaseType (CCG.typeOfAtom elseA) of
        CT.NotBaseType -> X.throw (ExpectedBaseType orig (CCG.typeOfAtom elseA))
        CT.AsBaseType btr -> do
          atom <- mkAtom (CCG.App (CCE.BaseIte btr (CCG.AtomExpr testA) (CCG.AtomExpr resA) (CCG.AtomExpr elseA)))
          return (Some atom, ext)
    (test, res) : rest ->
      withStaticTest test
        (translateExpr' res ty)
        (translateIfExpr orig rest elseExpr ty) $ do
      (Some trA, extRest) <- translateIfExpr orig rest elseExpr ty
      Some testA <- translateExpr test
      (Some resA, extRes) <- translateExpr' res (mergeConstraints ty (someTypeOfAtom trA))
      ext <- mergeExtensions extRes extRest
      Refl <- assertAtomType test CT.BoolRepr testA
      Refl <- assertAtomType res (CCG.typeOfAtom trA) resA
      case CT.asBaseType (CCG.typeOfAtom trA) of
        CT.NotBaseType -> X.throw (ExpectedBaseType orig (CCG.typeOfAtom trA))
        CT.AsBaseType btr -> do
          atom <- mkAtom (CCG.App (CCE.BaseIte btr (CCG.AtomExpr testA) (CCG.AtomExpr resA) (CCG.AtomExpr trA)))
          return (Some atom, ext)

maskToBVs :: AS.Mask -> (AS.Expr, AS.Expr)
maskToBVs mask = (AS.ExprLitBin $ map maskBitToSet mask, AS.ExprLitBin $ map maskBitToRequired mask)
  where
    maskBitToSet mb = case mb of
      AS.MaskBitSet -> True
      AS.MaskBitUnset -> False
      AS.MaskBitEither -> False

    maskBitToRequired mb = case mb of
       AS.MaskBitSet -> True
       AS.MaskBitUnset -> True
       AS.MaskBitEither -> False

-- | Translate set element tests
--
-- Single element tests are translated into a simple equality test
--
-- Ranges are translated as a conjunction of inclusive tests. x IN [5..10] => 5 <= x && x <= 10
translateSetElementTest :: AS.Expr
                        -> CCG.Atom s tp
                        -> AS.SetElement
                        -> Generator h s arch ret (CCG.Expr (ASLExt arch) s CT.BoolType)
translateSetElementTest e0 a0 elt =
  case elt of
    AS.SetEltSingle expr@(AS.ExprLitMask mask) -> do
      let ty = CCG.typeOfAtom a0
      let (setMaskE, requiredMaskE) = maskToBVs mask
      Some setMask <- translateExpr setMaskE
      Some requiredMask <- translateExpr requiredMaskE
      Refl <- assertAtomType setMaskE ty setMask
      Refl <- assertAtomType requiredMaskE ty requiredMask
      -- zero-out 'either' bits from the mask in our source bitvector
      Some maskedBV <- bvBinOp CCE.BVAnd (e0, a0) (requiredMaskE, requiredMask)
      -- test if the result is equivalent to the mandatory set bits from the mask
      Some testAtom <- applyBinOp eqOp
        (AS.ExprBinOp AS.BinOpBitwiseAnd e0 requiredMaskE, maskedBV) (setMaskE, setMask)
      Refl <- assertAtomType expr CT.BoolRepr testAtom
      return (CCG.AtomExpr testAtom)

    AS.SetEltSingle expr -> do
      Some atom1 <- translateExpr expr
      Refl <- assertAtomType expr (CCG.typeOfAtom a0) atom1
      Some atom2 <- applyBinOp eqOp (e0, a0) (expr, atom1)
      Refl <- assertAtomType expr CT.BoolRepr atom2
      return (CCG.AtomExpr atom2)
    AS.SetEltRange lo hi -> do
      Some loA <- translateExpr lo
      Some hiA <- translateExpr hi
      Refl <- assertAtomType lo (CCG.typeOfAtom a0) loA
      Refl <- assertAtomType hi (CCG.typeOfAtom a0) hiA
      Some loTest <- applyBinOp leOp (lo, loA) (e0, a0)
      Some hiTest <- applyBinOp leOp (e0, a0) (hi, hiA)
      Refl <- assertAtomType lo CT.BoolRepr loTest
      Refl <- assertAtomType hi CT.BoolRepr hiTest
      return (CCG.App (CCE.And (CCG.AtomExpr loTest) (CCG.AtomExpr hiTest)))


disjoin :: (CCE.IsSyntaxExtension ext)
        => CCG.Expr ext s CT.BoolType
        -> CCG.Expr ext s CT.BoolType
        -> CCG.Expr ext s CT.BoolType
disjoin p1 p2 = CCG.App (CCE.Or p1 p2)


-- ** Arithmetic and comparison operations

{- | The core arithmetic, bitwise and comparison operations are a straightforward
transformation, with the exception that ASL can implicity cast
integers as bitvectors. e.g: @0101 + 2 = 0111@.
-}

-- | Translate a given ASL binary operation ('AS.BinOp') over two
-- expressions ('AS.Expr') under some 'TypeConstraint' for the resulting
-- type.
translateBinaryOp :: forall h s ret arch
                   . AS.BinOp
                  -> AS.Expr
                  -> AS.Expr
                  -> TypeConstraint
                  -> Generator h s arch ret (Some (CCG.Atom s))
translateBinaryOp op e1 e2 tc = do
  let (tc1, tc2) = constraintsOfArgs op tc
  (Some a1, _) <- translateExpr' e1 tc1
  (Some a2, _) <- translateExpr' e2 tc2
  let p1 = (e1, a1)
  let p2 = (e2, a2)
  env <- getStaticEnv
  case op of
    AS.BinOpPlusPlus -> X.throw (UnsupportedBinaryOperator op)
    AS.BinOpLogicalAnd -> logicalBinOp CCE.And p1 p2
    AS.BinOpLogicalOr -> logicalBinOp CCE.Or p1 p2
    AS.BinOpBitwiseOr -> bvBinOp CCE.BVOr p1 p2
    AS.BinOpBitwiseAnd -> bvBinOp CCE.BVAnd p1 p2
    AS.BinOpBitwiseXor -> bvBinOp CCE.BVXor p1 p2
    AS.BinOpEQ -> applyBinOp eqOp p1 p2
    AS.BinOpNEQ -> do
      Some atom <- applyBinOp eqOp p1 p2
      Refl <- assertAtomType (AS.ExprBinOp op e1 e2) CT.BoolRepr atom
      Some <$> mkAtom (CCG.App (CCE.Not (CCG.AtomExpr atom)))
    AS.BinOpGT -> do
      -- NOTE: We always use unsigned comparison for bitvectors - is that correct?
      Some atom <- applyBinOp leOp p1 p2
      Refl <- assertAtomType (AS.ExprBinOp op e1 e2) CT.BoolRepr atom
      Some <$> mkAtom (CCG.App (CCE.Not (CCG.AtomExpr atom)))
    AS.BinOpLTEQ -> applyBinOp leOp p1 p2
    AS.BinOpLT -> applyBinOp ltOp p1 p2
    AS.BinOpGTEQ -> do
      Some atom <- applyBinOp ltOp p1 p2
      Refl <- assertAtomType (AS.ExprBinOp op e1 e2) CT.BoolRepr atom
      Some <$> mkAtom (CCG.App (CCE.Not (CCG.AtomExpr atom)))
    AS.BinOpAdd -> applyBinOp addOp p1 p2
    AS.BinOpSub -> applyBinOp subOp p1 p2
    AS.BinOpMul -> applyBinOp mulOp p1 p2
    AS.BinOpMod -> applyBinOp modOp p1 p2
    --FIXME: REM is only used once in mapvpmw, is it just mod there?
    AS.BinOpRem -> applyBinOp modOp p1 p2
    AS.BinOpDiv -> applyBinOp divOp p1 p2
    AS.BinOpShiftLeft -> bvBinOp CCE.BVShl p1 p2
    AS.BinOpShiftRight -> bvBinOp CCE.BVLshr p1 p2
    -- FIXME: What is the difference between BinOpDiv and BinOpDivide?
    AS.BinOpConcat -> do
      BVRepr n1 <- getAtomBVRepr a1
      BVRepr n2 <- getAtomBVRepr a2
      Just n1PosProof <- return $ WT.isPosNat n1
      WT.LeqProof <- return $ WT.leqAdd n1PosProof n2
      Some <$> mkAtom (CCG.App (CCE.BVConcat n1 n2 (CCG.AtomExpr a1) (CCG.AtomExpr a2)))
    AS.BinOpPow
      | Just (StaticInt 2) <- SE.exprToStatic env e1 -> do
        Refl <- assertAtomType e2 CT.IntegerRepr a2
        let nr = WT.knownNat @128
        let shift = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr a2)
        let base = CCG.App $ CCE.BVLit nr (BV.one nr)
        let shifted = CCG.App $ (CCE.BVShl nr base shift)
        Some <$> mkAtom (sbvToInteger nr shifted)

    _ -> X.throw (UnsupportedBinaryOperator op)

-- Linear Arithmetic operators

addOp :: BinaryOperatorBundle h s arch ret 'SameK
addOp = BinaryOperatorBundle (mkBVBinOP CCE.BVAdd) (mkBinOP CCE.NatAdd) (mkBinOP CCE.IntAdd)

subOp :: BinaryOperatorBundle h s arch ret 'SameK
subOp = BinaryOperatorBundle (mkBVBinOP CCE.BVSub) (mkBinOP CCE.NatSub) (mkBinOP CCE.IntSub)

-- Nonlinear Arithmetic operators

-- For now we hide these behind uninterpreted functions until we have a better story
-- for when we actually need their theories

-- mulOp :: BinaryOperatorBundle ext s 'SameK
-- mulOp = BinaryOperatorBundle CCE.BVMul CCE.NatMul CCE.IntMul

-- modOp :: BinaryOperatorBundle ext s 'SameK
-- modOp = BinaryOperatorBundle (error "BV mod not supported") CCE.NatMod CCE.IntMod

-- divOp :: BinaryOperatorBundle ext s 'SameK
-- divOp = BinaryOperatorBundle (error "BV div not supported") CCE.NatDiv CCE.IntDiv

mkBinUF :: T.Text
        -> CCG.Expr (ASLExt arch) s tp
        -> CCG.Expr (ASLExt arch) s tp
        -> Generator h s arch ret (CCG.Atom s tp)
mkBinUF nm arg1E arg2E = do
  arg1 <- mkAtom arg1E
  arg2 <- mkAtom arg2E
  Just (Some atom, _) <- translateFunctionCall (AS.VarName nm) [Some arg1, Some arg2] ConstraintNone
  Refl <- assertAtomType' (CCG.typeOfAtom arg1) atom
  return atom

mulOp :: BinaryOperatorBundle h s arch ret 'SameK
mulOp = BinaryOperatorBundle (\_ -> mkBinUF "BVMul") (mkBinUF "NatMul") (mkBinUF "IntMul")

modOp :: BinaryOperatorBundle h s arch ret 'SameK
modOp = BinaryOperatorBundle (error "BV mod not supported") (mkBinUF "NatMod") (mkBinUF "IntMod")

divOp :: BinaryOperatorBundle h s arch ret 'SameK
divOp = BinaryOperatorBundle (error "BV div not supported") (mkBinUF "NatDiv") (mkBinUF "IntDiv")


realmulOp :: BinaryOperatorBundle h s arch ret 'SameK
realmulOp = BinaryOperatorBundle (mkBVBinOP CCE.BVMul) (mkBinOP CCE.NatMul) (mkBinOP CCE.IntMul)

realmodOp :: BinaryOperatorBundle h s arch ret 'SameK
realmodOp = BinaryOperatorBundle (error "BV mod not supported") (mkBinOP CCE.NatMod) (mkBinOP CCE.IntMod)

realdivOp :: BinaryOperatorBundle h s arch ret 'SameK
realdivOp = BinaryOperatorBundle (error "BV div not supported") (mkBinOP CCE.NatDiv) (mkBinOP CCE.IntDiv)

-- Comparison operators

eqOp :: BinaryOperatorBundle h s arch ret 'BoolK
eqOp = BinaryOperatorBundle (mkBVBinOP CCE.BVEq) (mkBinOP CCE.NatEq) (mkBinOP CCE.IntEq)

leOp :: BinaryOperatorBundle h s arch ret 'BoolK
leOp = BinaryOperatorBundle (mkBVBinOP CCE.BVUle) (mkBinOP CCE.NatLe) (mkBinOP CCE.IntLe)

ltOp :: BinaryOperatorBundle h s arch ret 'BoolK
ltOp = BinaryOperatorBundle (mkBVBinOP CCE.BVUlt) (mkBinOP CCE.NatLt) (mkBinOP CCE.IntLt)


mkBVBinOP :: (a -> b -> c -> CCE.App (ASLExt arch) (CCR.Expr (ASLExt arch) s) tp) -> (a -> b -> c -> Generator h s arch ret (CCG.Atom s tp))
mkBVBinOP f a b c = do
  mkAtom (CCG.App (f a b c))

mkBinOP :: (a -> b -> CCE.App (ASLExt arch) (CCR.Expr (ASLExt arch) s) tp) -> (a -> b -> Generator h s arch ret (CCG.Atom s tp))
mkBinOP f a b = do
  mkAtom (CCG.App (f a b))

data ReturnK = BoolK
             -- ^ Tag used for comparison operations, which always return BoolType
             | SameK
             -- ^ Tag used for other operations, which preserve the type

type family BinaryOperatorReturn (r :: ReturnK) (tp :: CT.CrucibleType) where
  BinaryOperatorReturn 'BoolK tp = CT.BoolType
  BinaryOperatorReturn 'SameK tp = tp


data BinaryOperatorBundle h s arch ret (rtp :: ReturnK) =
  BinaryOperatorBundle { obBV :: forall n . (1 WT.<= n) => WT.NatRepr n -> CCG.Expr (ASLExt arch) s (CT.BVType n) -> CCG.Expr (ASLExt arch) s (CT.BVType n) -> Generator h s arch ret (CCG.Atom s (BinaryOperatorReturn rtp (CT.BVType n)))
                       , obNat :: CCG.Expr (ASLExt arch) s CT.NatType -> CCG.Expr (ASLExt arch) s CT.NatType -> Generator h s arch ret (CCG.Atom s (BinaryOperatorReturn rtp CT.NatType))
                       , obInt :: CCG.Expr (ASLExt arch) s CT.IntegerType -> CCG.Expr (ASLExt arch) s CT.IntegerType -> Generator h s arch ret (CCG.Atom s (BinaryOperatorReturn rtp CT.IntegerType))
                       }

applyBinOp' :: BinaryOperatorBundle h s arch ret rtp
             -> (Maybe AS.Expr, CCG.Atom s tp1)
             -> (Maybe AS.Expr, CCG.Atom s tp2)
             -> Generator h s arch ret (Some (CCG.Atom s))
applyBinOp' bundle (e1, a1) (e2, a2) =
  case CCG.typeOfAtom a1 of
    CT.BVRepr nr -> do
      case CCG.typeOfAtom a2 of
        CT.IntegerRepr -> do
            let a2' = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr a2)
            Some <$> obBV bundle nr (CCG.AtomExpr a1) a2'
        _ -> do
          Refl <- assertAtomType'' e2 (CT.BVRepr nr) a2
          Some <$> obBV bundle nr (CCG.AtomExpr a1) (CCG.AtomExpr a2)
    CT.NatRepr -> do
      Refl <- assertAtomType'' e2 CT.NatRepr a2
      Some <$> obNat bundle (CCG.AtomExpr a1) (CCG.AtomExpr a2)
    CT.IntegerRepr -> do
      case CCG.typeOfAtom a2 of
        CT.BVRepr nr -> do
          let a1' = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr a1)
          Some <$> obBV bundle nr a1' (CCG.AtomExpr a2)
        _ -> do
          Refl <- assertAtomType'' e2 CT.IntegerRepr a2
          Some <$> obInt bundle (CCG.AtomExpr a1) (CCG.AtomExpr a2)
    CT.BoolRepr -> do
      case CCG.typeOfAtom a2 of
        CT.BoolRepr -> do
          let nr = WT.knownNat @1
          let a1' = CCG.App $ CCE.BoolToBV nr (CCG.AtomExpr a1)
          let a2' = CCG.App $ CCE.BoolToBV nr (CCG.AtomExpr a2)
          Some <$> obBV bundle nr a1' a2'
        _ -> X.throw (UnsupportedComparisonType e1 (CCG.typeOfAtom a1))

    _ -> X.throw (UnsupportedComparisonType e1 (CCG.typeOfAtom a1))

-- | Apply a binary operator to two operands, performing the necessary type checks
applyBinOp :: BinaryOperatorBundle h s arch ret rtp
             -> (AS.Expr, CCG.Atom s tp1)
             -> (AS.Expr, CCG.Atom s tp2)
             -> Generator h s arch ret (Some (CCG.Atom s))
applyBinOp bundle (e1, a1) (e2, a2) = applyBinOp' bundle (Just e1, a1) (Just e2, a2)

bvBinOp :: (ext ~ ASLExt arch)
        => (forall n . (1 WT.<= n) => WT.NatRepr n -> CCG.Expr ext s (CT.BVType n) -> CCG.Expr ext s (CT.BVType n) -> CCE.App ext (CCG.Expr ext s) (CT.BVType n))
        -> (AS.Expr, CCG.Atom s tp1)
        -> (AS.Expr, CCG.Atom s tp2)
        -> Generator h s arch ret (Some (CCG.Atom s))
bvBinOp con (e1, a1) (e2, a2) =
  case CCG.typeOfAtom a1 of
    CT.BVRepr nr -> do
      case CCG.typeOfAtom a2 of
        CT.IntegerRepr -> do
          let a2' = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr a2)
          Some <$> mkAtom (CCG.App (con nr (CCG.AtomExpr a1) a2'))
        _ -> do
          Refl <- assertAtomType e2 (CT.BVRepr nr) a2
          Some <$> mkAtom (CCG.App (con nr (CCG.AtomExpr a1) (CCG.AtomExpr a2)))
    CT.IntegerRepr -> do
      case CCG.typeOfAtom a2 of
        CT.BVRepr nr -> do
          let a1' = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr a1)
          Some <$> mkAtom (CCG.App (con nr a1' (CCG.AtomExpr a2)))
        CT.IntegerRepr -> do
          -- the de-integerization in the final normalized spec will reverse this
          -- to just be the given bitvector operation on the actual bitvectors underlying
          -- the given integers
          let bvrepr = WT.knownNat @128
          let a1' = integerToSBV bvrepr (CCG.AtomExpr a1)
          let a2' = integerToSBV bvrepr (CCG.AtomExpr a2)
          Some <$> mkAtom (sbvToInteger bvrepr (CCG.App (con bvrepr a1' a2')))
        _ -> throwTrace (ExpectedBVType e1 (CCG.typeOfAtom a2))
    _ -> throwTrace $ (ExpectedBVType e1 (CCG.typeOfAtom a1))

logicalBinOp :: (ext ~ ASLExt arch)
             => (CCG.Expr ext s CT.BoolType -> CCG.Expr ext s CT.BoolType -> CCE.App ext (CCG.Expr ext s) CT.BoolType)
             -> (AS.Expr, CCG.Atom s tp1)
             -> (AS.Expr, CCG.Atom s tp2)
             -> Generator h s arch ret (Some (CCG.Atom s))
logicalBinOp con (e1, a1) (e2, a2) = do
  Refl <- assertAtomType e1 CT.BoolRepr a1
  Refl <- assertAtomType e2 CT.BoolRepr a2
  Some <$> mkAtom (CCG.App (con (CCG.AtomExpr a1) (CCG.AtomExpr a2)))

-- | Translate a unary operation into Crucible
translateUnaryOp :: AS.UnOp
                 -> AS.Expr
                 -> Generator h s arch ret (Some (CCG.Atom s))
translateUnaryOp op expr = do
  Some atom <- translateExpr expr
  case op of
    AS.UnOpNot -> do
      case CCG.typeOfAtom atom of
        CT.BVRepr nr -> do
          Some <$> mkAtom (CCG.App (CCE.BVNot nr (CCG.AtomExpr atom)))
        CT.BoolRepr -> do
          Some <$> mkAtom (CCG.App (CCE.Not (CCG.AtomExpr atom)))
        _ -> throwTrace $ UnexpectedExprType (Just expr) (CCG.typeOfAtom atom) (CT.BoolRepr)
    AS.UnOpNeg ->
      case CCG.typeOfAtom atom of
        CT.IntegerRepr -> do
          Some <$> mkAtom (CCG.App (CCE.IntNeg (CCG.AtomExpr atom)))
        _ -> throwTrace $ UnexpectedExprType (Just expr) (CCG.typeOfAtom atom) (CT.BoolRepr)

-- * Types

-- | Translate types (including user-defined types) into Crucible type reprs
--
-- Translations of user-defined types (i.e., types defined in an ASL program)
-- are stored in the 'TranslationState' and are looked up when needed.
--
translateType :: AS.Type -> Generator h s arch ret (Some CT.TypeRepr)
translateType t = do
  env <- getStaticEnv
  t' <- case applyStaticEnv env t of
    Just t' -> return $ t'
    Nothing -> throwTrace $ CannotStaticallyEvaluateType t (staticEnvMapVals env)
  case t' of
    AS.TypeRef (AS.QualifiedIdentifier _ "integer") -> return (Some CT.IntegerRepr)
    AS.TypeRef (AS.QualifiedIdentifier _ "boolean") -> return (Some CT.BoolRepr)
    AS.TypeRef (AS.QualifiedIdentifier _ "bit") -> return (Some (CT.BVRepr (NR.knownNat @1)))
    AS.TypeRef qi@(AS.QualifiedIdentifier _ ident) -> do
      uts <- MS.gets tsUserTypes
      case Map.lookup ident uts of
        Nothing -> X.throw (UnexpectedType qi)
        Just (Some ut) -> return (Some (CT.baseToType (userTypeRepr ut)))
    AS.TypeFun "bits" e ->
      case e of
        AS.ExprLitInt nBits
          | Just (Some nr) <- NR.someNat nBits
          , Just NR.LeqProof <- NR.isPosNat nr -> return (Some (CT.BVRepr nr))
        _ -> throwTrace $ UnsupportedType t'
    AS.TypeFun "__RAM" (AS.ExprLitInt n)
       | Just (Some nRepr) <- NR.someNat n
       , Just NR.LeqProof <- NR.isPosNat nRepr ->
         return $ Some $ CT.baseToType $
           WT.BaseArrayRepr (Ctx.empty Ctx.:> WT.BaseBVRepr (WT.knownNat @52)) (WT.BaseBVRepr nRepr)
    AS.TypeArray t'' (AS.IxTypeRange (AS.ExprLitInt _) (AS.ExprLitInt _)) -> do
      Some ty <- asBaseType <$> translateType t''
      return $ Some $ CT.SymbolicArrayRepr (Ctx.empty Ctx.:> WT.BaseIntegerRepr) ty    
    AS.TypeArray _ty _idxTy -> throwTrace $ UnsupportedType t'    
    AS.TypeFun _ _ -> throwTrace $ UnsupportedType t'

    AS.TypeReg _i _flds -> throwTrace $ UnsupportedType t'
    _ -> throwTrace $ UnsupportedType t'

-- * Function Calls

-- | Translate a function call into Crucible as an uninterpreted
-- function. Function calls may be either from a 'AS.Stmt' or an 'AS.Expr',
-- where the latter may produce some 'CCG.Atom' its return value. The given
-- 'InputArgument' is either an 'AS.Expr' in the usual case, but may also be a
-- 'CCG.Atom' used for calling functions internally with Crucible values.
--
-- The given arguments are unified against the function signature with 'unifyArgs'.
--
-- The current value of all global variables is passed to function, and the resulting
-- value of globals from its result are written to the current global state.
translateFunctionCall :: forall e arch h s ret
                       . InputArgument s e
                      => AS.QualifiedIdentifier
                      -> [e]
                      -> TypeConstraint
                      -> Generator h s arch ret (Maybe (Some (CCG.Atom s), ExtendedTypeData))
translateFunctionCall qIdent args ty = do
  logMsg 2 $ "CALL: " <> (T.pack (show qIdent))
  sigMap <- MS.gets tsFunctionSigs
  let ident = mkFunctionName qIdent (length args)
  case Map.lookup ident sigMap of
    Nothing -> throwTrace $ MissingFunctionDefinition ident
    Just (SomeSimpleFunctionSignature sig) -> do
      (finalIdent, argAtoms, Some retT) <- unifyArgs ident (zip (sfuncArgs sig) args) (sfuncRet sig) ty
      case Ctx.fromList argAtoms of
        Some argAssign -> do
          let atomTypes = FC.fmapFC CCG.typeOfAtom argAssign

          withGlobals (sfuncGlobalReadReprs sig) $ \globalReprs globals -> do
            let globalsType = CT.baseToType (WT.BaseStructRepr globalReprs)
            globalsSnapshot <- liftGenerator $ CCG.extensionStmt (GetRegState globalReprs globals)
            let vals = FC.fmapFC CCG.AtomExpr argAssign
            let ufGlobalRep = WT.BaseStructRepr (FC.fmapFC projectValue (sfuncGlobalWriteReprs sig))
            let ufCtx = (Ctx.empty Ctx.:> ufGlobalRep Ctx.:> retT)
            let uf = UF finalIdent UFCached (WT.BaseStructRepr ufCtx) (atomTypes Ctx.:> globalsType) (vals Ctx.:> globalsSnapshot)
            atom <- mkAtom (CCG.App (CCE.ExtensionApp uf))
            let globalResult = GetBaseStruct (CT.SymbolicStructRepr ufCtx) Ctx.i1of2 (CCG.AtomExpr atom)
            withGlobals (sfuncGlobalWriteReprs sig) $ \_ thisGlobals -> liftGenerator $ do
              _ <- CCG.extensionStmt (SetRegState thisGlobals (CCG.App $ CCE.ExtensionApp globalResult))
              return ()
            let returnResult = GetBaseStruct (CT.SymbolicStructRepr ufCtx) Ctx.i2of2 (CCG.AtomExpr atom)
            result <- mkAtom (CCG.App $ CCE.ExtensionApp returnResult)
            case retT of
              WT.BaseStructRepr ctx@(Ctx.Empty Ctx.:> _) -> do
                let [ret] = sfuncRet sig
                ext <- mkExtendedTypeData ret
                let retTC = CT.SymbolicStructRepr ctx
                let returnResult' = GetBaseStruct retTC (Ctx.baseIndex) (CCG.AtomExpr result)
                unboxedResult <- mkAtom (CCG.App $ CCE.ExtensionApp returnResult')
                return $ Just $ (Some unboxedResult, ext)
              WT.BaseStructRepr Ctx.Empty -> return Nothing
              WT.BaseStructRepr _ -> do
                exts <- mapM mkExtendedTypeData (sfuncRet sig)
                return $ Just $ (Some result, TypeTuple exts)
              _ -> throwTrace $ BadASLFunctionCall

    -- At the cost of adding significant complexity to the CFG, we *could* attempt to terminate early
    -- whenever undefined or unpredictable behavior is encountered from a called function.
    -- This seems excessive, since we can always check these flags at the toplevel.

    -- EndOfInstruction, however, should retain the processor state while avoiding any
    -- additional instruction processing.

    -- We only need to perform this check if the global writes set of a called function could
    -- possibly have updated the end of instruction flag.

    -- FIXME: We are not checking early exit currently as it turned out to be too expensive.
    -- We are better off doing an intelligent analysis of when it is feasible for an instruction
    -- to have finished processing.

    -- checkEarlyExit :: forall tp ctx
    --                 . CCG.Atom s (CT.SymbolicStructType ctx)
    --                -> Ctx.Index ctx tp
    --                -> LabeledValue T.Text WT.BaseTypeRepr tp
    --                -> Generator h s arch ret ()
    -- checkEarlyExit struct idx (LabeledValue globName rep) = do
    --   if globName `elem` [endofinstructionVarName]
    --   then do
    --     let testE = GetBaseStruct (CCG.typeOfAtom struct) idx (CCG.AtomExpr struct)
    --     test <- mkAtom $ CCG.App $ CCE.ExtensionApp $ testE
    --     Refl <- assertAtomType' CT.BoolRepr test
    --     liftGenerator2 (abnormalExit ov) (return ()) $ \exit ret ->
    --       CCG.ifte_ (CCG.AtomExpr test) exit ret
    --   else return ()

-- | Obtain the current value of all the give globals
-- This is a subset of all of the global state (and a subset of the current
-- global state).
withGlobals :: forall m h s arch ret globals r
             . (m ~ Generator h s arch ret)
            => Ctx.Assignment (LabeledValue T.Text WT.BaseTypeRepr) globals
            -> (Ctx.Assignment WT.BaseTypeRepr globals -> Ctx.Assignment BaseGlobalVar globals -> m r)
            -> m r
withGlobals reprs k = do
  globMap <- MS.gets tsGlobals
  let globReprs = FC.fmapFC projectValue reprs
  globals <- FC.traverseFC (fetchGlobal globMap) reprs
  k globReprs globals
  where
    fetchGlobal :: forall tp . Map.Map T.Text (Some CCG.GlobalVar)
                -> LabeledValue T.Text WT.BaseTypeRepr tp
                -> m (BaseGlobalVar tp)
    fetchGlobal globMap (LabeledValue globName rep)
      | Just (Some gv) <- Map.lookup globName globMap
      , Just Refl <- testEquality (CT.baseToType rep) (CCG.globalType gv) =
          return $ BaseGlobalVar gv
      | otherwise = throwTrace $ TranslationError $ "withGlobals: Missing global (or wrong type): " ++ show globName


-- | Unify the given list of arguments against the given 'AS.Type'.
-- Arguments are unified in order, augmenting the current static typing
-- environment with any discovered bindings during type unification.
unifyArgs :: InputArgument s e
          => T.Text
          -> [(FunctionArg, e)]
          -> [AS.Type]
          -> TypeConstraint
          -> Generator h s arch ret
               (T.Text, [Some (CCG.Atom s)], Some WT.BaseTypeRepr)
unifyArgs fnname fargs rets constraint = do
  let args = map (\((FunctionArg nm t), e)  -> ((nm, t), e)) fargs
  outerState <- MS.get
  freshState <- freshLocalsState
  (atoms, retT, tenv) <- withState freshState $ do
      mapM_ (\(decl, e) -> collectStaticValues outerState decl e) args
      atoms <- mapM (\(decl, e) -> unifyArg outerState decl e) args
      unifyRet rets constraint
      retsT <- mapM translateType rets
      let retT = mkBaseStructRepr (map asBaseType retsT)
      tenv <- getStaticEnv
      return (atoms, retT, tenv)
  let dvars = concat $ map dependentVarsOfType rets ++ map (\((_,t), _) -> dependentVarsOfType t) args
  listenv <- mapM (getConcreteValue tenv) dvars
  let env = Map.fromList listenv
  hdl <- MS.gets tsHandle
  MST.liftST (STRef.modifySTRef hdl (Set.insert (fnname,env)))
  return (mkFinalFunctionName env fnname, atoms, retT)
  where
    unifyRet :: [AS.Type] -- return type of function
             -> TypeConstraint -- potential concrete target type
             -> Generator h s arch ret ()
    unifyRet [t] constraint' = unifyType t constraint'
    unifyRet ts constraints' = unifyTypes ts constraints'

    getConcreteValue env nm = case staticEnvValue env nm of
      Just i -> return (nm, i)
      _ -> throwTrace $ CannotMonomorphizeFunctionCall fnname (staticEnvMapVals env)

-- | Unify a syntactic ASL type against a crucible type, and update
-- the current static variable evironment with any discovered instantiations
unifyType :: AS.Type
          -> TypeConstraint
          -> Generator h s arch ret ()
unifyType aslT constraint = do
  env <- getStaticEnv
  case (aslT, constraint) of
    (AS.TypeFun "bits" expr, ConstraintSingle (CT.BVRepr repr)) ->
      case expr of
        AS.ExprLitInt i | Just (Some nr) <- NR.someNat i, Just Refl <- testEquality repr nr -> return ()
        AS.ExprVarRef (AS.QualifiedIdentifier _ ident) ->
          case staticEnvValue env ident of
            Just (StaticInt i) | Just (Some nr) <- NR.someNat i, Just Refl <- testEquality repr nr -> return ()
            Nothing -> mapStaticVals (Map.insert ident (StaticInt $ toInteger (NR.natValue repr)))
            _ -> throwTrace $ TypeUnificationFailure aslT constraint (staticEnvMapVals env)
        AS.ExprBinOp AS.BinOpMul e e' ->
          case (mInt env e, mInt env e') of
            (Left i, Left i') | Just (Some nr) <- NR.someNat (i * i'), Just Refl <- testEquality repr nr -> return ()
            (Right (AS.ExprVarRef (AS.QualifiedIdentifier _ ident)), Left i')
              | reprVal <- toInteger $ WT.natValue repr
              , (innerVal, 0) <- reprVal `divMod` i' ->
                mapStaticVals $ Map.insert ident (StaticInt innerVal)
            (Left i, Right (AS.ExprVarRef (AS.QualifiedIdentifier _ ident)))
              | reprVal <- toInteger $ WT.natValue repr
              , (innerVal, 0) <- reprVal `divMod` i ->
               mapStaticVals $ Map.insert ident (StaticInt innerVal)
            _ -> throwTrace $ TypeUnificationFailure aslT constraint (staticEnvMapVals env)
        _ -> throwTrace $ TypeUnificationFailure aslT constraint (staticEnvMapVals env)
    (AS.TypeArray t (AS.IxTypeRange (AS.ExprLitInt _) (AS.ExprLitInt _)),
      ConstraintSingle (CT.SymbolicArrayRepr (Ctx.Empty Ctx.:> WT.BaseIntegerRepr) repr)) -> do
      unifyType t (ConstraintSingle (CT.baseToType repr))

    -- it's not clear if this is always safe

    -- (AS.TypeFun "bits" _ , ConstraintHint (HintMaxBVSize nr)) -> do
    --   case applyStaticEnv' env aslT of
    --     Just _ -> return ()
    --     _ -> unifyType aslT (ConstraintSingle (CT.BVRepr nr))
    (_, ConstraintHint _) -> return ()
    (_, ConstraintNone) -> return ()
    (_, ConstraintTuple _) -> throwTrace $ TypeUnificationFailure aslT constraint (staticEnvMapVals env)
    (_, ConstraintSingle cTy) -> do
      Some atomT' <- translateType aslT
      case testEquality cTy atomT' of
        Just Refl -> return ()
        _ -> throwTrace $ TypeUnificationFailure aslT constraint (staticEnvMapVals env)
  where
    mInt env e = case SE.exprToStatic env e of
      Just (StaticInt i) -> Left i
      _ -> Right e

unifyTypes :: [AS.Type]
           -> TypeConstraint
           -> Generator h s arch ret ()
unifyTypes tps constraint = do
  case constraint of
    ConstraintSingle (CT.SymbolicStructRepr stps) |
        insts <- zip tps (FC.toListFC (ConstraintSingle . CT.baseToType) stps)
      , length insts == length tps ->
          mapM_ (\(tp, stp) -> unifyType tp stp) insts
    ConstraintTuple cts
      | length tps == length cts ->
        mapM_ (\(tp, ct) -> unifyType tp ct) (zip tps cts)
    ConstraintNone -> return ()
    _ -> X.throw $ TypesUnificationFailure tps constraint

getConcreteTypeConstraint :: AS.Type -> Generator h s arch ret TypeConstraint
getConcreteTypeConstraint t = do
  env <- getStaticEnv
  case applyStaticEnv env t of
    Just t' -> do
      Some ty <- translateType t'
      return $ ConstraintSingle ty
    _ -> return $ ConstraintNone

someTypeOfAtom :: CCG.Atom s tp
               -> TypeConstraint
someTypeOfAtom atom = ConstraintSingle (CCG.typeOfAtom atom)


class InputArgument s t where
  unifyArg :: TranslationState arch h ret s
           -> AS.SymbolDecl
           -> t
           -> Generator h s arch ret (Some (CCG.Atom s))
  collectStaticValues :: TranslationState arch h ret s
                      -> AS.SymbolDecl
                      -> t
                      -> Generator h s arch ret ()

instance InputArgument s AS.Expr where
  unifyArg outerState (_, t) e = do
    cty <- getConcreteTypeConstraint t
    (Some atom, _) <- withState outerState $ translateExpr' e cty
    unifyType t (ConstraintSingle (CCG.typeOfAtom atom))
    return $ Some atom

  collectStaticValues outerState (nm, _) e = do
    sv <- withState outerState $ do
      env <- getStaticEnv
      return $ SE.exprToStatic env e
    case sv of
      Just i -> mapStaticVals (Map.insert nm i)
      _ -> return ()

instance InputArgument s (Some (CCG.Atom s)) where
  unifyArg _ (_, t) (Some atom) = do
    unifyType t (ConstraintSingle (CCG.typeOfAtom atom))
    return (Some atom)
  collectStaticValues _ _ _ = return ()

instance InputArgument s Void where
  unifyArg _ _ v = Void.absurd v
  collectStaticValues _ _ v = Void.absurd v

-- * Variable Lookup

-- | Look up the current value of a given variable, throwing an exception
-- if it is not found.
lookupVarRef :: forall arch h s ret
             . T.Text
            -> Generator h s arch ret (Some (CCG.Expr (ASLExt arch) s))
lookupVarRef name = do
  mref <- lookupVarRef' name
  case mref of
    Just ref -> return ref
    Nothing -> throwTrace $ UnboundName name

-- | This wrapper is used as a uniform return type in 'lookupVarRef', as each of
-- the lookup types (arguments, locals, or globals) technically return different
-- values, but they are values that are pretty easy to handle uniformly.
--
-- We could probably get rid of this wrapper if we made a function like
-- @withVarValue@ that took a continuation instead.
data ExprConstructor arch regs h s ret where
  ExprConstructor :: a tp
                  -> (a tp -> Generator h s arch ret (CCG.Expr (ASLExt arch) s tp))
                  -> ExprConstructor (ASLExt arch) regs h s ret


lookupVarRef' :: forall arch h s ret
              . T.Text
             -> Generator h s arch ret (Maybe (Some (CCG.Expr (ASLExt arch) s)))
lookupVarRef' name = do
  ts <- MS.get
  env <- getStaticEnv
  case (lookupLocalConst env <|>
        lookupArg ts <|>
        lookupRef ts <|>
        lookupGlobalStruct ts <|>
        lookupGlobal ts <|>
        lookupEnum ts <|>
        lookupConst ts) of
    Just (ExprConstructor e con) -> Just <$> Some <$> con e
    Nothing -> return Nothing
  where
    lookupLocalConst env = do
      sv <- staticEnvValue env name
      case sv of
        StaticInt i -> return (ExprConstructor (CCG.App (CCE.IntLit i)) return)
        StaticBool b -> return (ExprConstructor (CCG.App (CCE.BoolLit b)) return)
        StaticBV bv -> case bitsToBVExpr bv of
          Some bve -> return (ExprConstructor bve return)

    lookupArg ts = do
      Some e <- Map.lookup name (tsArgAtoms ts)
      return (ExprConstructor (CCG.AtomExpr e) return)
    lookupRef ts = do
      Some r <- Map.lookup name (tsVarRefs ts)
      return (ExprConstructor r $ (liftGenerator . CCG.readReg))
    lookupGlobalStruct _ = do
      if name `elem` globalStructNames
        then return (ExprConstructor (CCG.App CCE.EmptyApp) $ return)
        else fail ""
    lookupGlobal ts = do
      Some g <- Map.lookup name (tsGlobals ts)
      return (ExprConstructor g $ (liftGenerator . CCG.readGlobal))
    lookupEnum ts = do
      (Some n, i) <- Map.lookup name (tsEnums ts)
      Just NR.LeqProof <- return $ NR.isPosNat n
      return (ExprConstructor (CCG.App $ CCE.IntegerToBV n (CCG.App (CCE.IntLit i))) return)
    lookupConst ts = do
      Some (ConstVal repr e) <- Map.lookup name (tsConsts ts)
      case repr of
        WT.BaseBoolRepr -> return (ExprConstructor (CCG.App (CCE.BoolLit e)) return)
        WT.BaseIntegerRepr -> return (ExprConstructor (CCG.App (CCE.IntLit e)) return)
        WT.BaseBVRepr wRepr ->
          return (ExprConstructor (CCG.App (CCE.BVLit wRepr e)) return)
        _ -> error "bad const type"

lookupGlobalLabel :: LabeledValue T.Text WT.BaseTypeRepr tp
                  -> Generator h s arch ret (CCG.Expr (ASLExt arch) s (CT.BaseToType tp))
lookupGlobalLabel lblv = do
  globals <- MS.gets tsGlobals
  case Map.lookup (projectLabel lblv) globals of
    Just (Some glb) | Just Refl <- testEquality (CCG.globalType glb) (CT.baseToType (projectValue lblv)) ->
      liftGenerator $ CCG.readGlobal glb

    _ -> error $ "bad global:" ++ show lblv


-- | Look up the type of a variable.
lookupVarType :: forall arch h s ret
              . T.Text
             -> Generator h s arch ret (Maybe (Some (CT.TypeRepr)))
lookupVarType name = do
  f <- lookupVarType'
  return $ f name

lookupVarType' :: Generator h s arch ret (T.Text -> Maybe (Some (CT.TypeRepr)))
lookupVarType' = do
  ts <- MS.get
  svals <- MS.gets tsStaticValues
  return $ \name ->
    let
      lookupLocalConst = do
        sv <- Map.lookup name svals
        case typeOfStatic sv of
          StaticIntType -> return $ Some CT.IntegerRepr
          StaticBoolType -> return $ Some CT.BoolRepr
          StaticBVType sz -> case intToBVRepr sz of
            Some (BVRepr nr) -> return $ Some $ CT.BVRepr nr
      lookupArg = do
        Some e <- Map.lookup name (tsArgAtoms ts)
        return $ Some $ CCG.typeOfAtom e
      lookupRef = do
        Some r <- Map.lookup name (tsVarRefs ts)
        return $ Some $ CCG.typeOfReg r
      lookupGlobal = do
        Some g <- Map.lookup name (tsGlobals ts)
        return $ Some $ CCG.globalType g
      lookupEnum = do
        _ <- Map.lookup name (tsEnums ts)
        return $ Some $ CT.IntegerRepr
      lookupConst = do
        Some (ConstVal repr _) <- Map.lookup name (tsConsts ts)
        return $ Some $ CT.baseToType repr
    in
      lookupLocalConst <|>
      lookupArg <|>
      lookupRef <|>
      lookupGlobal <|>
      lookupEnum <|>
      lookupConst

-- | The distinguished name of the global variable that represents the bit of
-- information indicating that the processor is in the UNPREDICTABLE state
--
-- We simulate the UNPREDICATABLE and UNDEFINED ASL statements with virtual
-- processor state.
unpredictableVarName :: T.Text
unpredictableVarName = T.pack "__UnpredictableBehavior"

-- | The distinguished name of the global variable that represents the bit of
-- state indicating that the processor is in the UNDEFINED state.
undefinedVarName :: T.Text
undefinedVarName = T.pack "__UndefinedBehavior"

-- | The distinguished name of the global variable that represents the bit of
-- state indicating that an assertion has been tripped.
assertionfailureVarName :: T.Text
assertionfailureVarName = T.pack "__AssertionFailure"

--  The distinguished name of the global variable that represents the bit of
-- state indicating that instruction processing is finished
-- FIXME: Currently unused.
_endofinstructionVarName :: T.Text
_endofinstructionVarName = T.pack "__EndOfInstruction"

assertExpr :: AS.Expr
           -> T.Text
           -> Generator h s arch ret ()
assertExpr e msg = do
  (Some res) <- translateExpr e
  Refl <- assertAtomType e CT.BoolRepr res
  assertAtom res (Just e) msg


crucibleToStaticType :: Some CT.TypeRepr -> Maybe StaticType
crucibleToStaticType (Some ct) = case ct of
  CT.IntegerRepr -> Just $ StaticIntType
  CT.BoolRepr -> Just $ StaticBoolType
  CT.BVRepr nr -> Just $ StaticBVType (WT.intValue nr)
  _ -> Nothing

getStaticEnv :: Generator h s arch ret StaticEnvMap
getStaticEnv = do
  svals <- MS.gets tsStaticValues
  tlookup <- lookupVarType'
  return $ StaticEnvMap svals (staticTypeMap tlookup)
  where
    staticTypeMap f nm =
      fromMaybe Nothing $ crucibleToStaticType <$> (f nm)

-- | Convert an lVal to its equivalent expression.
lValToExpr :: AS.LValExpr -> Maybe AS.Expr
lValToExpr lval = case lval of
  AS.LValVarRef qName -> return $ AS.ExprVarRef qName
  AS.LValMember lv memberName -> do
    lve <- lValToExpr lv
    return $ AS.ExprMember lve memberName
  AS.LValArrayIndex lv slices -> do
    lve <- lValToExpr lv
    return $ AS.ExprIndex lve slices
  AS.LValSliceOf lv slices -> do
    lve <- lValToExpr lv
    return $ AS.ExprSlice lve slices
  _ -> Nothing

mkSliceRange :: (Integer, Integer) -> AS.Slice
mkSliceRange (lo, hi) = AS.SliceRange (AS.ExprLitInt hi) (AS.ExprLitInt lo)




sbvToInteger :: forall w s arch
              . 1 WT.<= w
             => NR.NatRepr w
             -> CCG.Expr (ASLExt arch) s (CT.BVType w)
             -> CCG.Expr (ASLExt arch) s CT.IntegerType
sbvToInteger w bv =
  let uf = UF ("sbvToInteger_" <> T.pack (show (WT.intValue w)))
            UFCached WT.BaseIntegerRepr (Ctx.singleton (CT.BVRepr w)) (Ctx.singleton bv)
  in CCG.App $ CCE.ExtensionApp uf

integerToSBV :: forall w s arch
                    . 1 WT.<= w
                   => NR.NatRepr w
                   -> CCG.Expr (ASLExt arch) s CT.IntegerType
                   -> CCG.Expr (ASLExt arch) s (CT.BVType w)
integerToSBV w ie =
  let uf = UF ("uu_integerToSBV_" <> T.pack (show (WT.intValue w)))
            UFCached (WT.BaseBVRepr w) (Ctx.singleton CT.IntegerRepr) (Ctx.singleton ie)
  in CCG.App $ CCE.ExtensionApp uf

mkUF :: T.Text -> CT.TypeRepr tp -> Generator h s arch ret (CCG.Atom s tp)
mkUF nm repr' = do
  let repr = asBaseType' repr'
  Just Refl <- return $ toFromBaseProof repr'
  let uf = UF nm UFFresh repr Ctx.empty Ctx.empty
  mkAtom (CCG.App (CCE.ExtensionApp uf))

mkExtendedTypeData :: AS.Type
                   -> Generator h s arch ret (ExtendedTypeData)
mkExtendedTypeData = mkExtendedTypeData' getUT getExtendedTypeData
  where
    getUT :: T.Text -> Generator h s arch ret (Maybe (Some UserType))
    getUT tpName = Map.lookup tpName <$> MS.gets tsUserTypes

-- | Add any additional 'ExtendedTypeData' to the given variable implied
-- by the given 'AS.Type'
addExtendedTypeData :: AS.Identifier
                    -- ^ the name of the variable to be assigned extended type data
                    -> AS.Type
                    -- ^ the type potentially implying 'ExtendedTypeData' 
                    -> Generator h s arch ret ()
addExtendedTypeData ident ty = do
  ext <- mkExtendedTypeData ty
  putExtendedTypeData ident ext

putExtendedTypeData :: AS.Identifier
                    -> ExtendedTypeData
                    -> Generator h s arch ret ()
putExtendedTypeData ident ext' = do
  ext'' <- getExtendedTypeData ident
  ext <- mergeExtensions ext' ext''
  MS.modify' $ \s -> s { tsExtendedTypes = Map.insert ident ext (tsExtendedTypes s) }

getExtendedTypeData :: AS.Identifier
                    -> Generator h s arch ret (ExtendedTypeData)
getExtendedTypeData ident = do
  exts <- MS.gets tsExtendedTypes
  return $ fromMaybe TypeBasic (Map.lookup ident exts)

mergeExtensions :: ExtendedTypeData
                -> ExtendedTypeData
                -> Generator h s arch ret (ExtendedTypeData)
mergeExtensions ext1 ext2 =
  case (ext1, ext2) of
  (_, TypeBasic) -> return ext1
  (TypeBasic, _) -> return ext2
  _ -> if ext1 == ext2 then return ext1
    else return TypeBasic


withState :: TranslationState arch h ret s
          -> Generator h s arch ret a
          -> Generator h s arch ret a
withState s f = do
  s' <- MS.get
  MS.put s
  r <- f
  MS.put s'
  return r

forgetNewStatics :: Generator h s arch ret a
                 -> Generator h s arch ret a
forgetNewStatics f = do
  svals <- MS.gets tsStaticValues
  r <- f
  MS.modify' $ \s -> s { tsStaticValues = svals }
  return r

-- Return a translation state that doesn't contain any local variables from
-- the current translation context
freshLocalsState :: Generator h s arch ret (TranslationState arch h ret s)
freshLocalsState = do
  s <- MS.get
  return $ s { tsArgAtoms = Map.empty
             , tsVarRefs = Map.empty
             , tsExtendedTypes = Map.empty
             , tsStaticValues = Map.empty
             }

mapStaticVals :: (Map.Map T.Text StaticValue -> Map.Map T.Text StaticValue)
             -> Generator h s arch ret ()
mapStaticVals f = do
  env <- MS.gets tsStaticValues
  MS.modify' $ \s -> s { tsStaticValues = f env }


dependentVarsOfType :: AS.Type -> [T.Text]
dependentVarsOfType t = case t of
  AS.TypeFun "bits" e -> TR.varsOfExpr e
  AS.TypeArray t' _ -> dependentVarsOfType t'
  _ -> []


asBaseType :: Some CT.TypeRepr -> Some WT.BaseTypeRepr
asBaseType (Some t) = case CT.asBaseType t of
  CT.AsBaseType bt -> Some bt
  CT.NotBaseType -> error $ "Expected base type: " <> show t

asBaseType' :: CT.TypeRepr tp -> WT.BaseTypeRepr (ToBaseType tp)
asBaseType' t = case CT.asBaseType t of
  CT.AsBaseType bt -> bt
  CT.NotBaseType -> error $ "Expected base type: " <> show t


assertAtomType'' :: Maybe AS.Expr
               -- ^ Expression that was translated
               -> CT.TypeRepr tp1
               -- ^ Expected type
               -> CCG.Atom s tp2
               -- ^ Translation (which contains the actual type)
               -> Generator h s arch ret (tp1 :~: tp2)
assertAtomType'' mexpr expectedRepr atom =
  case testEquality expectedRepr (CCG.typeOfAtom atom) of
    Nothing -> throwTrace (UnexpectedExprType mexpr (CCG.typeOfAtom atom) expectedRepr)
    Just Refl -> return Refl

assertAtomType' :: CT.TypeRepr tp1
                -- ^ Expected type
                -> CCG.Atom s tp2
                -- ^ Translation (which contains the actual type)
                -> Generator h s arch ret (tp1 :~: tp2)
assertAtomType' expectedRepr atom = assertAtomType'' Nothing expectedRepr atom

assertAtomType :: AS.Expr
               -- ^ Expression that was translated
               -> CT.TypeRepr tp1
               -- ^ Expected type
               -> CCG.Atom s tp2
               -- ^ Translation (which contains the actual type)
               -> Generator h s arch ret (tp1 :~: tp2)
assertAtomType expr expectedRepr atom = assertAtomType'' (Just expr) expectedRepr atom


data BVRepr tp where
  BVRepr :: (tp ~ CT.BVType w, 1 WT.<= w) => WT.NatRepr w -> BVRepr tp

getAtomBVRepr :: CCG.Atom s tp
              -> Generator h s arch ret (BVRepr tp)
getAtomBVRepr atom =
  case CCG.typeOfAtom atom of
    CT.BVRepr wRepr -> return $ BVRepr wRepr
    tp -> throwTrace $ ExpectedBVType' Nothing tp


getStaticValue :: AS.Expr
               -> Generator h s arch ret (Maybe (StaticValue))
getStaticValue expr = do
  env <- getStaticEnv
  return $ SE.exprToStatic env expr


-- This is not necessarily complete
constraintsOfArgs :: AS.BinOp -> TypeConstraint -> (TypeConstraint, TypeConstraint)
constraintsOfArgs bop tc = case bop of
  AS.BinOpAdd -> (tc, tc)
  AS.BinOpSub -> (tc, tc)
  _ -> (ConstraintNone, ConstraintNone)

intToBVRepr :: Integer -> Some (BVRepr)
intToBVRepr nBits = do
  case NR.mkNatRepr (fromIntegral nBits) of
   Some nr
     | Just NR.LeqProof <- NR.testLeq (NR.knownNat @1) nr ->
       Some $ BVRepr nr
     | otherwise -> X.throw InvalidZeroLengthBitvector

bitsToBVExpr :: [Bool] -> Some (CCG.Expr (ASLExt arch) s)
bitsToBVExpr bits = do
  case intToBVRepr (fromIntegral $ length bits) of
   Some (BVRepr nr) -> Some $ CCG.App $ CCE.BVLit nr (BV.mkBV nr (bitsToInteger bits))




withStaticTest :: AS.Expr
               -> Generator h s arch ret a
               -> Generator h s arch ret a
               -> Generator h s arch ret a
               -> Generator h s arch ret a
withStaticTest test ifTrue ifFalse ifUnknown = do
  env <- getStaticEnv
  case SE.exprToStatic env test of
    Just (StaticBool True) -> ifTrue
    Just (StaticBool False) -> ifFalse
    _ -> ifUnknown

-- FIXME: This implies some kind of ordering on constraints
mergeConstraints :: TypeConstraint -> TypeConstraint -> TypeConstraint
mergeConstraints ty1 ty2 = case (ty1, ty2) of
  (ConstraintNone, _) -> ty2
  (_, ConstraintNone) -> ty1
  (ConstraintSingle _, _) -> ty1
  (_, ConstraintSingle _) -> ty2
  (ConstraintHint HintAnyBVSize, ConstraintHint (HintMaxBVSize _)) -> ty2
  (ConstraintHint (HintMaxBVSize _), ConstraintHint HintAnyBVSize) -> ty1
  (ConstraintHint HintAnyBVSize, ConstraintHint (HintMaxSignedBVSize _)) -> ty2
  (ConstraintHint (HintMaxSignedBVSize _), ConstraintHint HintAnyBVSize) -> ty1
  _ -> error $ "Incompatible type constraints: " ++ show ty1 ++ " " ++ show ty2



data BVAtomPair s where
  BVAtomPair :: (tp ~ CT.BVType w, 1 WT.<= w)
             => WT.NatRepr w
             -> CCG.Atom s tp
             -> CCG.Atom s tp
             -> BVAtomPair s

-- zero-extend one bitvector to match the other's size
matchBVSizes :: CCG.Atom s tp
             -> CCG.Atom s tp'
             -> Generator h s arch ret (BVAtomPair s)
matchBVSizes atom1 atom2 = do
  BVRepr wRepr1 <- getAtomBVRepr atom1
  BVRepr wRepr2 <- getAtomBVRepr atom2
  case wRepr1 `WT.testNatCases` wRepr2 of
    WT.NatCaseEQ ->
      return $ BVAtomPair wRepr1 atom1 atom2
    WT.NatCaseLT WT.LeqProof -> do
      atom1' <- mkAtom (CCG.App (CCE.BVZext wRepr2 wRepr1 (CCG.AtomExpr atom1)))
      return $ BVAtomPair wRepr2 atom1' atom2
    WT.NatCaseGT WT.LeqProof -> do
      atom2' <- mkAtom (CCG.App (CCE.BVZext wRepr1 wRepr2 (CCG.AtomExpr atom2)))
      return $ BVAtomPair wRepr1 atom1 atom2'

extBVAtom :: 1 WT.<= w
           => Bool
           -> WT.NatRepr w
           -> CCG.Atom s tp
           -> Generator h s arch ret (CCG.Atom s (CT.BVType w))
extBVAtom signed repr atom = do
  BVRepr atomRepr <- getAtomBVRepr atom
  case atomRepr `WT.testNatCases` repr of
    WT.NatCaseEQ ->
      return atom
    WT.NatCaseLT WT.LeqProof -> do
      let bop = if signed then CCE.BVSext else CCE.BVZext
      atom' <- mkAtom (CCG.App (bop repr atomRepr (CCG.AtomExpr atom)))
      return atom'
    _ -> throwTrace $ UnexpectedBitvectorLength (CT.BVRepr atomRepr) (CT.BVRepr repr)

relaxConstraint :: TypeConstraint -> TypeConstraint
relaxConstraint constraint = case constraint of
  ConstraintSingle (CT.BVRepr nr) -> ConstraintHint (HintMaxBVSize nr)
  _ -> constraint

-- Overrides that dispatch to ambiguous function overloads based on the argument type
overloadedDispatchOverrides :: AS.Expr
                            -> TypeConstraint
                            -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
overloadedDispatchOverrides e tc = case e of
  AS.ExprCall (AS.QualifiedIdentifier q "Align") args@[e1, _] -> Just $ do
    Some atom1 <- translateExpr e1
    nm <- case CCG.typeOfAtom atom1 of
      CT.IntegerRepr ->
        return $ "Alignintegerinteger"
      CT.BVRepr _ ->
        return $ "AlignbitsNinteger"
      x -> error $ "Unexpected override type:" ++ show x
    translateExpr' (AS.ExprCall (AS.QualifiedIdentifier q nm) args) ConstraintNone
  AS.ExprCall (AS.QualifiedIdentifier q fun) args@[e1, e2]
    | fun `elem` ["Min","Max"]
    -> Just $ do
    Some atom1 <- translateExpr e1
    Some atom2 <- translateExpr e2
    Refl <- assertAtomType e1 CT.IntegerRepr atom1
    Refl <- assertAtomType e2 CT.IntegerRepr atom2
    translateExpr' (AS.ExprCall (AS.QualifiedIdentifier q (fun <> "integerinteger")) args) tc
  _ ->  mkFaultOv "IsExternalAbort" <|>
        mkFaultOv "IsAsyncAbort" <|>
        mkFaultOv "IsSErrorInterrupt" <|>
        mkFaultOv "IsExternalSyncAbort"
  where
    mkFaultOv nm =
      case e of
        AS.ExprCall (AS.QualifiedIdentifier q nm') [arg] | nm == nm' -> Just $ do
          (_, ext) <- translateExpr' arg ConstraintNone
          ov <- case ext of
            TypeStruct _ -> return $ "FaultRecord"
            _ -> return $ "Fault"
          translateExpr' (AS.ExprCall (AS.QualifiedIdentifier q (nm <> ov)) [arg]) tc
        _ -> Nothing

getBVLength :: Maybe AS.Expr
            -> TypeConstraint
            -> Generator h s arch ret (Some BVRepr)
getBVLength mexpr ty = do
  env <- getStaticEnv
  case () of
    _ | Just e <- mexpr
      , Just (StaticInt i) <- SE.exprToStatic env e
      , Just (Some repr) <- WT.someNat i
      , Just WT.LeqProof <- (WT.knownNat @1) `WT.testLeq` repr ->
        return $ Some $ BVRepr repr
    _ | ConstraintSingle (CT.BVRepr nr) <- ty ->
        return $ Some $ BVRepr $ nr
    _ | ConstraintHint (HintMaxBVSize nr) <- ty ->
        return $ Some $ BVRepr $ nr
    _ -> throwTrace $ CannotDetermineBVLength mexpr ty

-- This is a dead code path that no longer appears when all of the memory translation
-- functions are stubbed out.
  
-- getSymbolicBVLength :: AS.Expr
--                     -> Maybe (Generator h s arch ret (CCG.Atom s CT.IntegerType))
-- getSymbolicBVLength e = case e of
--     AS.ExprCall (AS.QualifiedIdentifier _ nm) [e]
--       | nm == "Zeros" || nm == "Ones" -> Just $ do
--         (Some argAtom) <- translateExpr overrides e
--         Refl <- assertAtomType e CT.IntegerRepr argAtom
--         mkAtom $ CCG.AtomExpr argAtom
--     AS.ExprLitBin bits -> Just $ do
--       mkAtom $ CCG.App $ CCE.IntLit $ fromIntegral $ length bits
--     AS.ExprSlice _ [slice] -> Just $ do
--       (loAtom, hiAtom) <- getSymbolicSliceRange overrides slice
--       mkAtom $ CCG.App $ CCE.IntSub (CCG.AtomExpr hiAtom) (CCG.AtomExpr loAtom)
--     AS.ExprVarRef (AS.QualifiedIdentifier _ ident) -> Just $ do
--       mTy <- lookupVarType ident
--       case mTy of
--         Just (Some (CT.BVRepr wRepr)) ->
--           mkAtom $ CCG.App $ CCE.IntLit $ WT.intValue wRepr
--         _ -> throwTrace $ UnboundName ident
--     AS.ExprBinOp AS.BinOpConcat e1 e2
--       | Just f1 <- getSymbolicBVLength e1
--       , Just f2 <- getSymbolicBVLength e2 -> Just $ f1 >>= \len1 -> f2 >>= \len2 ->
--         mkAtom $ CCG.App $ CCE.IntAdd (CCG.AtomExpr len1) (CCG.AtomExpr len2)
--     _ -> Nothing

list1ToMaybe :: [a] -> Maybe (Maybe a)
list1ToMaybe xs = case xs of
  [x] -> Just (Just x)
  [] -> Just Nothing
  _ -> Nothing

mkAtom' :: CCG.Expr (ASLExt arch) s tp
        -> Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData)
mkAtom' e = do
  atom <- mkAtom e
  return (Some atom, TypeBasic)

-- Overrides to handle cases where bitvector lengths cannot be
-- determined statically.
polymorphicBVOverrides :: forall h s arch ret
                        . AS.Expr
                       -> TypeConstraint
                       -> StaticEnvMap
                       -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
polymorphicBVOverrides expr ty env = case expr of
  AS.ExprBinOp bop arg1@(AS.ExprSlice _ _) arg2
    | bop == AS.BinOpEQ || bop == AS.BinOpNEQ -> Just $ do
        (Some atom1', _) <- translateExpr' arg1 (ConstraintHint HintAnyBVSize)
        BVRepr atom1sz <- getAtomBVRepr atom1'
        (Some atom2', _) <- translateExpr' arg2 (ConstraintHint $ HintMaxBVSize atom1sz)
        BVAtomPair _ atom1 atom2 <- matchBVSizes atom1' atom2'
        (Some result') <- applyBinOp eqOp (arg1, atom1) (arg2, atom2)
        Refl <- assertAtomType' CT.BoolRepr result'
        result <- case bop of
          AS.BinOpEQ -> return result'
          AS.BinOpNEQ -> mkAtom (CCG.App (CCE.Not (CCG.AtomExpr result')))
          _ -> error $ "Unexpected binary operation: " ++ show bop
        return (Some result, TypeBasic)
  AS.ExprBinOp AS.BinOpConcat expr1 (AS.ExprCall (AS.VarName "Zeros") [expr2])
    | Just (StaticInt 0) <- SE.exprToStatic env expr2 ->
      Just $ translateExpr' expr1 ty

  -- This is a dead code path that no longer appears when all of the memory translation
  -- functions are stubbed out.
  -- AS.ExprBinOp AS.BinOpConcat expr1 expr2
  --   | Just hint <- getConstraintHint ty
  --   , (mLen1 :: Maybe (Generator h s arch ret (CCG.Atom s CT.IntegerType))) <- getSymbolicBVLength expr1
  --   , (mLen2 :: Maybe (Generator h s arch ret (CCG.Atom s CT.IntegerType))) <- getSymbolicBVLength expr2
  --   , isJust mLen1 || isJust mLen2-> Just $ do
  --       (Some atom1', _) <- translateExpr' overrides expr1 (relaxConstraint ty)
  --       (Some atom2', _) <- translateExpr' overrides expr2 (relaxConstraint ty)
  --       BVAtomPair wRepr atom1 atom2 <- case hint of
  --         HintMaxSignedBVSize wRepr -> do
  --           atom1 <- extBVAtom False wRepr atom1' -- will inherit signed bits from atom2
  --           atom2 <- extBVAtom True wRepr atom2'
  --           return $ BVAtomPair wRepr atom1 atom2
  --         HintMaxBVSize wRepr -> do
  --           atom1 <- extBVAtom False wRepr atom1'
  --           atom2 <- extBVAtom False wRepr atom2'
  --           return $ BVAtomPair wRepr atom1 atom2
  --         HintAnyBVSize -> do
  --           matchBVSizes atom1' atom2'
  --       shift <- case (mLen1, mLen2) of
  --         (Just f1, _) -> f1 >>= \len1 ->
  --           return $ CCG.App $ CCE.IntegerToBV wRepr $ CCG.App $
  --             CCE.IntSub (CCG.App (CCE.IntLit $ WT.intValue wRepr)) (CCG.AtomExpr len1)
  --         (_, Just f2) -> f2 >>= \len2 ->
  --           return $ CCG.App $ CCE.IntegerToBV wRepr $ (CCG.AtomExpr len2)
  --       let atom1Shifted = CCG.App $ CCE.BVShl wRepr (CCG.AtomExpr atom1) shift

  --       result <- mkAtom $ CCG.App $ CCE.BVOr wRepr atom1Shifted (CCG.AtomExpr atom2)
  --       return (Some result, TypeBasic)

  AS.ExprCall (AS.QualifiedIdentifier _ "Int") [argExpr, isUnsigned] -> Just $ do
    Some unsigned <- translateExpr isUnsigned
    Refl <- assertAtomType' CT.BoolRepr unsigned

    (Some ubvatom, _) <- translateExpr' argExpr (ConstraintHint $ HintAnyBVSize)
    BVRepr unr <- getAtomBVRepr ubvatom
    uatom <- mkAtom $ CCG.App $ CCE.BvToInteger unr (CCG.AtomExpr ubvatom)

    (Some sbvatom, _) <- translateExpr' argExpr ConstraintNone
    BVRepr snr <- getAtomBVRepr sbvatom
    satom <- mkAtom $ sbvToInteger snr (CCG.AtomExpr sbvatom)
    Just Refl <- return $ testEquality unr snr

    mkAtom' $ CCG.App $ CCE.BaseIte CT.BaseIntegerRepr (CCG.AtomExpr unsigned) (CCG.AtomExpr uatom) (CCG.AtomExpr satom)
  AS.ExprCall (AS.QualifiedIdentifier _ "UInt") [argExpr] -> Just $ do
    (Some atom, _) <- translateExpr' argExpr (ConstraintHint $ HintAnyBVSize)
    BVRepr nr <- getAtomBVRepr atom
    mkAtom' (CCG.App (CCE.BvToInteger nr (CCG.AtomExpr atom)))

  AS.ExprCall (AS.QualifiedIdentifier _ "SInt") [argExpr] -> Just $ do
    Some atom <- translateExpr argExpr
    BVRepr nr <- getAtomBVRepr atom
    mkAtom' (sbvToInteger nr (CCG.AtomExpr atom))
  AS.ExprCall (AS.QualifiedIdentifier _ "IsZero") [argExpr] -> Just $ do
    (Some atom, _) <- translateExpr' argExpr (ConstraintHint $ HintAnyBVSize)
    BVRepr nr <- getAtomBVRepr atom
    mkAtom' (CCG.App (CCE.BVEq nr (CCG.AtomExpr atom) (CCG.App (CCE.BVLit nr (BV.zero nr)))))
  AS.ExprCall (AS.QualifiedIdentifier _ "IsOnes") [argExpr] -> Just $ do
    argExpr' <- case argExpr of
      AS.ExprSlice e slices ->
        return $ AS.ExprSlice (AS.ExprUnOp AS.UnOpNot e) slices
      _ -> return $ AS.ExprUnOp AS.UnOpNot argExpr
    translateExpr'
      (AS.ExprCall (AS.QualifiedIdentifier AS.ArchQualAny "IsZero") [argExpr'])
      ConstraintNone
  AS.ExprCall (AS.QualifiedIdentifier _ fun) (val : rest)
    | fun == "ZeroExtend" || fun == "SignExtend"
    , Just mexpr <- list1ToMaybe rest -> Just $ do
    Some (BVRepr targetWidth) <- getBVLength mexpr ty
    (Some valAtom, _) <- case fun of
      "ZeroExtend" -> translateExpr' val (ConstraintHint (HintMaxBVSize targetWidth))
      "SignExtend" -> translateExpr' val (ConstraintHint (HintMaxSignedBVSize targetWidth))
      _ -> error $ "Unexpected function name:" ++ show fun
    BVRepr valWidth <- getAtomBVRepr valAtom
    case valWidth `WT.testNatCases` targetWidth of
      WT.NatCaseEQ ->
        return $ (Some valAtom, TypeBasic)
      WT.NatCaseLT WT.LeqProof -> do
        atom <- case fun of
          "ZeroExtend" -> mkAtom (CCG.App (CCE.BVZext targetWidth valWidth (CCG.AtomExpr valAtom)))
          "SignExtend" -> mkAtom (CCG.App (CCE.BVSext targetWidth valWidth (CCG.AtomExpr valAtom)))
          _ -> error $ "Unexpected function name:" ++ show fun
        return $ (Some atom, TypeBasic)
      _ -> throwTrace $ ExpectedBVSizeLeq valWidth targetWidth
  AS.ExprCall (AS.QualifiedIdentifier _ fun) args
    | fun == "Zeros" || fun == "Ones"
    , Just mexpr <- list1ToMaybe args -> Just $ do
    Some (BVRepr targetWidth) <- getBVLength mexpr ty
    zeros <- mkAtom (CCG.App (CCE.BVLit targetWidth (BV.zero targetWidth)))
    case fun of
      "Zeros" -> return (Some zeros, TypeBasic)
      "Ones" -> mkAtom' (CCG.App $ CCE.BVNot targetWidth (CCG.AtomExpr zeros))
      _ -> error $ "Unexpected function name:" ++ show fun
  AS.ExprCall (AS.QualifiedIdentifier _ "Replicate") [AS.ExprLitBin [False], repe] -> Just $ do
    translateExpr'
     (AS.ExprCall (AS.QualifiedIdentifier AS.ArchQualAny "Zeros") [repe])
     ty
  AS.ExprCall (AS.QualifiedIdentifier _ fun@"Replicate") args@[bve, repe] -> Just $ do
    Some bvatom <- translateExpr bve
    case (SE.exprToStatic env repe, CCG.typeOfAtom bvatom) of
      (Just (StaticInt width), CT.BVRepr nr) |
          Just (Some rep) <- WT.someNat width
        , Just WT.LeqProof <- (WT.knownNat @1) `WT.testLeq` rep -> do
          mkAtom' $ replicateBV rep nr (CCG.AtomExpr bvatom)
      (Nothing, _) -> throwTrace $ RequiredConcreteValue repe (staticEnvMapVals env)
      _ -> throwTrace $ InvalidOverloadedFunctionCall fun args
  _ -> Nothing


replicateBV :: forall ext s rep w
             . 1 WT.<= w
            => 1 WT.<= rep
            => WT.NatRepr rep
            -> WT.NatRepr w
            -> CCG.Expr ext s (CT.BVType w)
            -> CCG.Expr ext s (CT.BVType (rep WT.* w))
replicateBV repRepr wRepr bv =
  if | predRepr <- WT.decNat repRepr -- rep - 1
     , mulRepr <- predRepr `WT.natMultiply` wRepr -- rep * w
     , Refl <- WT.minusPlusCancel repRepr (WT.knownNat @1) ->
       case WT.isZeroOrGT1 predRepr of
         Left Refl -> bv
         Right WT.LeqProof
           | WT.LeqProof <- WT.addPrefixIsLeq predRepr (WT.knownNat @1)
           , Refl <- WT.lemmaMul wRepr repRepr
           , Refl <- WT.plusMinusCancel predRepr (WT.knownNat @1)
           , WT.LeqProof <- WT.leqMulPos predRepr wRepr
           , WT.LeqProof <- WT.leqAdd (WT.leqProof (WT.knownNat @1) wRepr) mulRepr ->
             CCG.App $ CCE.BVConcat wRepr mulRepr bv (replicateBV predRepr wRepr bv)

-- Overrides for bitshifting functions
bitShiftOverrides :: forall h s arch ret
                        . AS.Expr
                       -> TypeConstraint
                       -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
bitShiftOverrides e _ = case e of
  AS.ExprCall (AS.QualifiedIdentifier _ "primitive_ASR") [x, shift] -> Just $ do
    Some xAtom <- translateExpr x
    Some shiftAtom <- translateExpr shift
    Refl <- assertAtomType shift CT.IntegerRepr shiftAtom
    BVRepr nr <- getAtomBVRepr xAtom
    let bvShift = CCG.App $ CCE.IntegerToBV nr (CCG.AtomExpr shiftAtom)
    result <- mkAtom (CCG.App $ CCE.BVAshr nr (CCG.AtomExpr xAtom) bvShift)
    return $ (Some result, TypeBasic)
  _ -> Nothing


-- Overrides for arithmetic
arithmeticOverrides :: forall h s arch ret
                        . AS.Expr
                       -> TypeConstraint
                       -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
arithmeticOverrides expr ty = case expr of
  AS.ExprCall (AS.VarName "primitive") [AS.ExprBinOp op e1 e2] -> Just $ do
    let (tc1, tc2) = constraintsOfArgs op ty
    (Some a1, _) <- translateExpr' e1 tc1
    (Some a2, _) <- translateExpr' e2 tc2
    let p1 = (e1, a1)
    let p2 = (e2, a2)
    satom <- case op of
      AS.BinOpMul -> applyBinOp realmulOp p1 p2
      AS.BinOpDiv -> applyBinOp realdivOp p1 p2
      AS.BinOpDivide -> applyBinOp realdivOp p1 p2
      AS.BinOpMod -> applyBinOp realmodOp p1 p2
      _ -> throwTrace $ UnsupportedExpr expr
    return (satom, TypeBasic)

  --FIXME: determine actual rounding here
  AS.ExprCall (AS.QualifiedIdentifier _ fun@"RoundTowardsZero") args@[e] -> Just $ do
    case e of
      (AS.ExprBinOp AS.BinOpDivide
        (AS.ExprCall (AS.QualifiedIdentifier _ "Real")
                       [e1])
        (AS.ExprCall (AS.QualifiedIdentifier _ "Real")
                       [e2]))
          -> translateExpr' (AS.ExprBinOp AS.BinOpDiv e1 e2) ty
      _ -> X.throw $ InvalidOverloadedFunctionCall fun args
  --FIXME: determine actual rounding here
  AS.ExprCall (AS.QualifiedIdentifier _ fun@"RoundUp") args@[e] -> Just $ do
    case e of
      (AS.ExprBinOp AS.BinOpDivide
        (AS.ExprCall (AS.QualifiedIdentifier _ "Real")
                       [e1])
        (AS.ExprCall (AS.QualifiedIdentifier _ "Real")
                       [e2]))
          -> translateExpr' (AS.ExprBinOp AS.BinOpDiv e1 e2) ty
      _ -> X.throw $ InvalidOverloadedFunctionCall fun args
  AS.ExprCall (AS.QualifiedIdentifier _ "NOT") [e] -> Just $ do
    translateExpr' (AS.ExprUnOp AS.UnOpNot e) ty
  AS.ExprCall (AS.QualifiedIdentifier _ "Abs") [e] -> Just $ do
    Some atom <- translateExpr e
    case CCG.typeOfAtom atom of
      CT.IntegerRepr -> do
        mkAtom' (CCG.App (CCE.IntAbs (CCG.AtomExpr atom)))
      tp -> X.throw $ ExpectedIntegerType e tp
  _ -> Nothing

constraintToBaseType :: TypeConstraint -> Maybe (Some (WT.BaseTypeRepr))
constraintToBaseType ty = case ty of
  ConstraintSingle tp | CT.AsBaseType bt <- CT.asBaseType tp -> return $ Some bt
  ConstraintTuple tys -> do
    Some tps <- Ctx.fromList <$> mapM constraintToBaseType tys
    return $ Some $ WT.BaseStructRepr tps
  _ -> fail ""

-- | Overrides for syntactic forms
--
-- Handles special cases in the ASL which are not covered by the normal
-- translation functions (e.g. calling built-in primitives or translating
-- sub-expressions under special type constraints).
data Overrides arch =
  Overrides { overrideStmt :: forall h s ret . AS.Stmt -> Maybe (Generator h s arch ret ())
            , overrideExpr :: forall h s ret . AS.Expr -> TypeConstraint -> StaticEnvMap -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
            }

-- | The standard set of ASL 'Overrides'
overrides :: forall arch . Overrides arch
overrides = Overrides {..}
  where overrideStmt :: forall h s ret . AS.Stmt -> Maybe (Generator h s arch ret ())

        overrideStmt stmt = case stmt of
          _ | Just ([], stmts) <- unletInStmt stmt -> Just $ do
              vars <- MS.gets tsVarRefs
              forgetNewStatics $ mapM_ translateStatement stmts
              MS.modify' $ \s -> s { tsVarRefs = vars }

          _ | Just (unvars, stmts) <- unletInStmt stmt -> Just $ do
              mapM_ translateStatement stmts
              MS.modify' $ \s -> s { tsVarRefs = foldr Map.delete (tsVarRefs s) unvars
                                   , tsStaticValues = foldr Map.delete (tsStaticValues s) unvars}

          _ | Just f <- unstaticBinding stmt -> Just $ do
                env <- getStaticEnv
                let (nm, sv) = f env
                mapStaticVals (Map.insert nm sv)

          _ | Just stmts <- unblockStmt stmt -> Just $ do
                mapM_ translateStatement stmts

          -- The Elem setter is inlined by the desugaring pass, so an explicit call should be a no-op
          AS.StmtCall (AS.VarName "SETTER_Elem") _ -> Just $ return ()

          -- Check for stubbed functions that should have been inlined elsewhere
          AS.StmtCall (AS.VarName "BadASLFunction") _ -> Just $ do
            throwTrace $ BadASLFunctionCall

          AS.StmtCall (AS.QualifiedIdentifier _ "ASLSetUndefined") [] -> Just $ do
            result <- mkAtom $ CCG.App $ CCE.BoolLit True
            translateAssignment' (AS.LValVarRef (AS.QualifiedIdentifier AS.ArchQualAny undefinedVarName)) result TypeBasic Nothing
            abnormalExit
          AS.StmtCall (AS.QualifiedIdentifier _ "ASLSetUnpredictable") [] -> Just $ do
            result <- mkAtom $ CCG.App $ CCE.BoolLit True
            translateAssignment' (AS.LValVarRef (AS.QualifiedIdentifier AS.ArchQualAny unpredictableVarName)) result TypeBasic Nothing
            abnormalExit
          AS.StmtCall (AS.QualifiedIdentifier _ "__abort") [] -> Just $ do
            translateStatement $ AS.StmtCall (AS.QualifiedIdentifier AS.ArchQualAny "EndOfInstruction") []
          AS.StmtCall (AS.QualifiedIdentifier q nm@"TakeHypTrapException") [arg] -> Just $ do
            (_, ext) <- translateExpr' arg ConstraintNone
            ov <- case ext of
              TypeStruct _ -> return $ "ExceptionRecord"
              _ -> return $ "integer"
            translateStatement (AS.StmtCall (AS.QualifiedIdentifier q (nm <> ov)) [arg])
          AS.StmtCall (AS.QualifiedIdentifier _ nm) [_]
            | nm `elem` ["print", "putchar"] -> Just $ do
              return ()
          _ -> Nothing

        overrideExpr :: forall h s ret
                      . AS.Expr
                     -> TypeConstraint
                     -> StaticEnvMap
                     -> Maybe (Generator h s arch ret (Some (CCG.Atom s), ExtendedTypeData))
        overrideExpr expr ty env =
          case expr of
            AS.ExprBinOp AS.BinOpEQ e mask@(AS.ExprLitMask _) -> Just $ do
              translateExpr' (AS.ExprInSet e [AS.SetEltSingle mask]) ty
            AS.ExprBinOp AS.BinOpNEQ e mask@(AS.ExprLitMask _) -> Just $ do
              translateExpr' (AS.ExprUnOp AS.UnOpNot (AS.ExprInSet e [AS.SetEltSingle mask])) ty
            AS.ExprCall (AS.QualifiedIdentifier _ "sizeOf") [x] -> Just $ do
              Some xAtom <- translateExpr x
              BVRepr nr <- getAtomBVRepr xAtom
              translateExpr' (AS.ExprLitInt (WT.intValue nr)) ConstraintNone
            AS.ExprCall (AS.VarName "truncate") [bvE, lenE] -> Just $ do
              Some bv <- translateExpr bvE
              BVRepr bvRepr <- getAtomBVRepr bv
              case SE.exprToStatic env lenE of
                Just (SE.StaticInt len)
                  | Some (BVRepr lenRepr) <- intToBVRepr len ->
                    case bvRepr `WT.testNatCases` lenRepr of
                      WT.NatCaseEQ -> return $ (Some bv, TypeBasic)
                      WT.NatCaseGT WT.LeqProof ->
                        mkAtom' $ CCG.App $ CCE.BVTrunc lenRepr bvRepr (CCG.AtomExpr bv)
                      WT.NatCaseLT _ ->
                        throwTrace $ UnexpectedBitvectorLength (CT.BVRepr lenRepr) (CT.BVRepr bvRepr)
                _ -> throwTrace $ RequiredConcreteValue lenE (staticEnvMapVals env)
            AS.ExprCall (AS.VarName "uninterpFnN") (AS.ExprLitString fnBaseName : nbitArgEs : allargEs)
              | Just (Some bty) <- constraintToBaseType ty
              , Just (SE.StaticInt nbitArgs) <- SE.exprToStatic env nbitArgEs -> Just $ do
                  let (bitSzEs, argEs) = splitAt (fromIntegral nbitArgs) allargEs
                  bitSzs <- forM bitSzEs $ \bitSzE -> do
                    case SE.exprToStatic env bitSzE of
                      Just (SE.StaticInt bitSz) -> return bitSz
                      _ -> throwTrace $ RequiredConcreteValue bitSzE (staticEnvMapVals env)
                  let fnName = fnBaseName <> "_" <> T.pack (List.intercalate "_" (map show bitSzs))
                  Some args <- Ctx.fromList <$> mapM translateExpr argEs
                  let uf = UF fnName UFCached bty (FC.fmapFC CCG.typeOfAtom args) (FC.fmapFC CCG.AtomExpr args)
                  atom <- mkAtom (CCG.App (CCE.ExtensionApp uf))
                  return (Some atom, TypeBasic)

            AS.ExprCall (AS.VarName "uninterpFn") (AS.ExprLitString fnName : argEs) -> Just $ do
              Some bty <- case constraintToBaseType ty of
                Just (Some bty) -> return $ Some bty
                Nothing -> throwTrace $ TranslationError $ "Unexpected type constraint for " ++ show expr ++ " " ++ show ty

              Some args <- Ctx.fromList <$> mapM translateExpr argEs
              let uf = UF fnName UFCached bty (FC.fmapFC CCG.typeOfAtom args) (FC.fmapFC CCG.AtomExpr args)
              atom <- mkAtom (CCG.App (CCE.ExtensionApp uf))
              return (Some atom, TypeBasic)
            _ ->
              polymorphicBVOverrides expr ty env <|>
              arithmeticOverrides expr ty <|>
              overloadedDispatchOverrides expr ty <|>
              bitShiftOverrides expr ty
