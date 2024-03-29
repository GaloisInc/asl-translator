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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}

module Language.ASL.SyntaxTraverse
  ( mkSyntaxOverrides
  , applySyntaxOverridesInstrs
  , applySyntaxOverridesDefs
  , varsOfExpr
  , SyntaxRepr(..)
  , KnownSyntaxRepr(..)
  , withKnownSyntaxRepr
  , useKnownSyntaxRepr
  , traverseExpr
  , traverseStmt
  , collectSyntax
  , mapSyntax
  , mkFunctionName
  , mapInnerName
  , collectWithLog
  , prettyShallowStmt
  , indentLog
  , unindentLog
  , pattern VarName
  )
where

import qualified Control.Applicative as App ( liftA2 )
import qualified Control.Monad.Writer.Lazy as W
import qualified Control.Monad.Identity as I
import qualified Control.Monad.Trans as MT
import qualified Language.ASL.Syntax as AS
import qualified Data.Text as T
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Maybe (maybeToList, catMaybes, isJust)
import           Language.ASL.Types
import qualified Data.Parameterized.Classes as PC

import           Util.Log ( MonadLog(..), indentLog, unindentLog )

pattern VarName :: T.Text -> AS.QualifiedIdentifier
pattern VarName nm <- AS.QualifiedIdentifier _ nm where
  VarName nm = AS.QualifiedIdentifier AS.ArchQualAny nm

varsOfExpr :: AS.Expr -> [T.Text]
varsOfExpr e = I.runIdentity $ collectSyntax getVar e
  where
    getVar :: forall t. KnownSyntaxRepr t => t -> I.Identity [T.Text]
    getVar = useKnownSyntaxRepr $ \syn -> \case
      SyntaxExprRepr
        | AS.ExprVarRef (VarName ident) <- syn ->
          return $ [ident]
      _ -> return $ []

-- | Syntactic-level expansions that should happen aggressively before
-- any interpretation.

applySyntaxOverridesDefs :: SyntaxMap -> [AS.Definition] -> [AS.Definition]
applySyntaxOverridesDefs f defs =
  let
     -- TODO: For sanity we delete setter definitions which require
    -- pass-by-reference since we don't have a sane semantics for this

    argName (AS.SetterArg name False) = Just name
    argName _ = Nothing

    mapDecl (i, t) = (i, f t)

    mapIxType ix = case ix of
      AS.IxTypeRange e e' -> AS.IxTypeRange (f e) (f e')
      _ -> ix

    mapDefs d = case d of
      AS.DefCallable qName args rets stmts ->
        [AS.DefCallable qName (mapDecl <$> args) (f <$> rets) (f <$> stmts)]
      AS.DefGetter qName args rets stmts ->
        [AS.DefCallable (mkGetterName (isJust args) qName)
         (mapDecl <$> (concat $ maybeToList args)) (f <$> rets) (f <$> stmts)]
      AS.DefSetter qName args rhs stmts -> maybeToList $ do
        argNames <- sequence (argName <$> (concat $ maybeToList args))
        Just $ AS.DefCallable { callableName = mkSetterName (isJust args) qName
                       , callableArgs = mapDecl <$> (rhs : argNames)
                       , callableRets = []
                       , callableStmts = f <$> stmts
                       }
      AS.DefConst i t e -> [AS.DefConst i (f t) (f e)]
      AS.DefTypeStruct i ds -> [AS.DefTypeStruct i (mapDecl <$> ds)]
      AS.DefArray i t ixt -> [AS.DefArray i (f t) (mapIxType ixt)]
      AS.DefVariable i t -> [AS.DefVariable i (f t)]
      _ -> [d]

  in concat $ mapDefs <$> defs

applySyntaxOverridesInstrs :: SyntaxMap -> [AS.Instruction] -> [AS.Instruction]
applySyntaxOverridesInstrs f instrs =
  let
    mapInstr (AS.Instruction instName instEncodings instPostDecode instExecute conditional) =
      AS.Instruction instName (mapEnc <$> instEncodings) (f <$> instPostDecode) (f <$> instExecute) conditional

    mapEnc (AS.InstructionEncoding a b c d encGuard encUnpredictable encDecode) =
      AS.InstructionEncoding a b c d (f <$> encGuard) encUnpredictable (f <$> encDecode)

  in mapInstr <$> instrs

data InternalOverride = InternalOverride
  { iovGetters :: Set.Set T.Text
  , iovSetters :: Set.Set T.Text
  }

emptyInternalOverride :: InternalOverride
emptyInternalOverride = InternalOverride Set.empty Set.empty

exprToLVal :: AS.Expr -> AS.LValExpr
exprToLVal expr = case expr of
  AS.ExprVarRef qident -> AS.LValVarRef qident
  AS.ExprIndex e slices -> AS.LValArrayIndex (exprToLVal e) slices
  AS.ExprSlice e slices -> AS.LValSliceOf (exprToLVal e) slices
  AS.ExprMembers e [mem] -> AS.LValMember (exprToLVal e) mem
  AS.ExprTuple es -> AS.LValTuple (map exprToLVal es)
  _ -> error $ "Invalid inline for expr:" <> show expr

mkSyntaxOverrides :: [AS.Definition] -> SyntaxMap
mkSyntaxOverrides defs =
  let
      addInternalOverride d iovrs = case d of
        AS.DefGetter qName (Just args) _ _ ->
          iovrs { iovGetters = Set.insert (mkFunctionName (mkGetterName True qName) (length args)) (iovGetters iovrs) }
        AS.DefGetter qName Nothing _ _ ->
          iovrs { iovGetters = Set.insert (mkFunctionName (mkGetterName False qName) 0) (iovGetters iovrs) }
        AS.DefSetter qName (Just args) _ _ ->
           iovrs { iovSetters = Set.insert (mkFunctionName (mkSetterName True qName) (length args + 1)) (iovSetters iovrs) }
        AS.DefSetter qName Nothing _ _ ->
           iovrs { iovSetters = Set.insert (mkFunctionName (mkSetterName False qName) 1) (iovSetters iovrs) }
        _ -> iovrs

      InternalOverride getters setters =
        foldr addInternalOverride emptyInternalOverride defs

      getSliceExpr slice = case slice of
        AS.SliceSingle e -> e
        _ -> error "Unexpected slice argument."

      assignOverrides lv = case lv of
        AS.LValArrayIndex (AS.LValVarRef (AS.QualifiedIdentifier _ "Elem"))
          [AS.SliceSingle vector, AS.SliceSingle e, AS.SliceSingle size] -> Just $ \rhs ->
          blockStmt $
            [ AS.StmtCall (AS.QualifiedIdentifier AS.ArchQualAny "SETTER_Elem") [rhs, vector, e, size]
            , stmtOverrides $
                AS.StmtAssign
                (AS.LValSliceOf (exprToLVal vector)
                 [(AS.SliceRange
                  (AS.ExprBinOp AS.BinOpSub
                   (AS.ExprBinOp AS.BinOpMul
                    (AS.ExprBinOp AS.BinOpAdd e (AS.ExprLitInt 1))
                    size)
                   (AS.ExprLitInt 1))
                  (AS.ExprBinOp AS.BinOpMul e size))]) rhs
            ]

        AS.LValArrayIndex (AS.LValVarRef (AS.QualifiedIdentifier q "Elem")) [vector, e] -> Just $ \rhs ->
          case assignOverrides (AS.LValArrayIndex (AS.LValVarRef (AS.QualifiedIdentifier q "Elem"))
                                [vector, e, AS.SliceSingle $ AS.ExprCall (AS.QualifiedIdentifier q "sizeOf") [rhs]]) of
            Just f -> f rhs
            Nothing -> error "Bad overrides"
        AS.LValArrayIndex (AS.LValVarRef qName) slices
          | Set.member (mkFunctionName (mkSetterName True qName) (length slices + 1)) setters ->
            Just $ (\rhs -> AS.StmtCall (mkSetterName True qName) (rhs : map getSliceExpr slices))
        AS.LValTuple lvs
          | lvs' <- map assignOverrides lvs
          , not $ null (catMaybes lvs') -> Just $ \rhs -> do
            let vars = take (length lvs') $
                  map (\i -> "__tupleResult" <> T.pack (show i)) ([0..] :: [Integer])
            let mkVar nm = AS.QualifiedIdentifier AS.ArchQualAny nm
            let getlv (i, (mlv', lv')) = case mlv' of
                  Just _ -> AS.LValVarRef (mkVar $ vars !! i)
                  _ -> lv'
            let tuple = map getlv (zip [0..] (zip lvs' lvs))
            let asnResult (i, mlv') = case mlv' of
                  Just lv' -> Just $ lv' (AS.ExprVarRef $ mkVar $ vars !! i)
                  Nothing -> Nothing
            let stmts' =
                  [ AS.StmtAssign (AS.LValTuple tuple) rhs ]
                  ++ catMaybes (map asnResult (zip [0..] lvs'))
            letInStmt vars stmts'

        AS.LValSliceOf (AS.LValArrayIndex (AS.LValVarRef qName) slices) outerSlices
          | Set.member (mkFunctionName (mkSetterName True qName) (length slices + 1)) setters ->
            Just $ \rhs -> do
              let getter = mkGetterName True qName
              let setter = mkSetterName True qName

              let mkIdent nm = AS.QualifiedIdentifier AS.ArchQualAny nm
              let mkVar nm = AS.ExprVarRef (mkIdent nm)
              let args = map getSliceExpr slices
              let old = "__oldGetterValue"
              let stmts =
                    [ AS.StmtAssign (AS.LValVarRef $ mkIdent old)
                       (AS.ExprCall getter args)
                    , AS.StmtAssign (AS.LValSliceOf (AS.LValVarRef $ mkIdent old) outerSlices)
                       rhs
                    , AS.StmtCall setter ((mkVar old) : args)
                    ]
              letInStmt [old] stmts
        AS.LValVarRef qName
          | Set.member (mkFunctionName (mkSetterName False qName) 1) setters ->
            Just $ \rhs -> AS.StmtCall (mkSetterName False qName) [rhs]
        _ -> Nothing

      stmtOverrides stmt = case stmt of
        AS.StmtAssign lv rhs
          | Just f <- assignOverrides lv ->
            f rhs
        AS.StmtUndefined -> mkCallStmt "ASLSetUndefined"
        AS.StmtUnpredictable -> mkCallStmt "ASLSetUnpredictable"
        AS.StmtSeeExpr {} -> mkCallStmt "ASLSetUndefined"
        AS.StmtSeeString {} -> mkCallStmt "ASLSetUndefined"
        _ -> stmt

      mkCallStmt nm = AS.StmtCall (AS.QualifiedIdentifier AS.ArchQualAny nm) []

      exprOverrides' expr = case expr of
        -- Limited support for alternate slice syntax
        AS.ExprIndex e slices@[AS.SliceOffset _ _] ->
          AS.ExprSlice e slices
        AS.ExprIndex e slices@[AS.SliceRange _ _] ->
          AS.ExprSlice e slices
        _ -> expr

      lvalOverrides lval = lval

      -- FIXME: This is a simple toplevel rewrite that assumes
      -- aliases and consts are never shadowed

      typeSynonyms = catMaybes $ typeSyn <$> defs
      typeSyn d = case d of
        AS.DefTypeAlias nm t -> Just (nm, t)
        _ -> Nothing

      typeSynMap = Map.fromList (typeSynonyms ++
                                 [(T.pack "signal", (AS.TypeFun "bits" (AS.ExprLitInt 1)))])

      typeOverrides t = case t of
        AS.TypeRef (AS.QualifiedIdentifier _ nm) ->
          case Map.lookup nm typeSynMap of
          Just t' -> t'
          Nothing -> t
        _ -> t


      varSynonyms = catMaybes $ varSyn <$> defs
      varSyn d = case d of
        AS.DefConst ident _ e -> Just (ident, e)
        _ -> Nothing

      varSynMap = Map.fromList varSynonyms

      exprOverrides e = case e of
        AS.ExprVarRef (AS.QualifiedIdentifier _ nm) -> case Map.lookup nm varSynMap of
          Just e' -> e'
          Nothing -> exprOverrides' e
        _ -> exprOverrides' e

      -- Given a bottom-up traversal, getter expansion needs to happen
      -- after all other rewrites, since apparent getters can actually
      -- be syntactic sugar for a getter/setter
      expandGetters expr = case expr of
        AS.ExprIndex (AS.ExprVarRef qName) slices
          | Set.member (mkFunctionName (mkGetterName True qName) (length slices)) getters ->
            AS.ExprCall (mkGetterName True qName) (map getSliceExpr slices)
        AS.ExprVarRef qName
          | Set.member (mkFunctionName (mkGetterName False qName) 0) getters ->
            AS.ExprCall (mkGetterName False qName) []
        _ -> expr

      firstMap :: forall t. KnownSyntaxRepr t => t -> t
      firstMap = withKnownSyntaxRepr $ \case
        SyntaxExprRepr -> exprOverrides
        SyntaxLValRepr -> lvalOverrides
        SyntaxStmtRepr -> stmtOverrides
        SyntaxTypeRepr -> typeOverrides
        _ -> id

      secondMap :: forall t. KnownSyntaxRepr t => t -> t
      secondMap = withKnownSyntaxRepr $ \case
        SyntaxExprRepr -> expandGetters
        _ -> id

  in (mapSyntax secondMap . mapSyntax firstMap)


-- | Representative type for major syntax elements
data SyntaxRepr t where
  SyntaxStmtRepr :: SyntaxRepr AS.Stmt
  SyntaxExprRepr :: SyntaxRepr AS.Expr
  SyntaxTypeRepr :: SyntaxRepr AS.Type
  SyntaxLValRepr :: SyntaxRepr AS.LValExpr
  SyntaxCallRepr :: SyntaxRepr (AS.QualifiedIdentifier, [AS.Expr])

instance PC.TestEquality SyntaxRepr where
  testEquality repr repr' = case (repr, repr') of
    (SyntaxStmtRepr, SyntaxStmtRepr) -> Just PC.Refl
    (SyntaxExprRepr, SyntaxExprRepr) -> Just PC.Refl
    (SyntaxTypeRepr, SyntaxTypeRepr) -> Just PC.Refl
    (SyntaxLValRepr, SyntaxLValRepr) -> Just PC.Refl
    (SyntaxCallRepr, SyntaxCallRepr) -> Just PC.Refl
    _ -> Nothing

deriving instance Eq (SyntaxRepr t)
deriving instance Ord (SyntaxRepr t)

class Show t => KnownSyntaxRepr t where
  knownSyntaxRepr :: SyntaxRepr t

withKnownSyntaxRepr :: KnownSyntaxRepr t => (SyntaxRepr t -> t -> a) -> t -> a
withKnownSyntaxRepr f = f knownSyntaxRepr

useKnownSyntaxRepr :: KnownSyntaxRepr t => (t -> SyntaxRepr t -> a) -> t -> a
useKnownSyntaxRepr f = (\t -> f t knownSyntaxRepr)

instance KnownSyntaxRepr AS.Stmt where
  knownSyntaxRepr = SyntaxStmtRepr

instance KnownSyntaxRepr AS.Expr where
  knownSyntaxRepr = SyntaxExprRepr

instance KnownSyntaxRepr AS.LValExpr where
  knownSyntaxRepr = SyntaxLValRepr

instance KnownSyntaxRepr AS.Type where
  knownSyntaxRepr = SyntaxTypeRepr

instance KnownSyntaxRepr (AS.QualifiedIdentifier, [AS.Expr]) where
  knownSyntaxRepr = SyntaxCallRepr


collectWithLog :: forall m a. MonadLog m => Integer -> (forall t. KnownSyntaxRepr t => t -> m a) -> (forall t. KnownSyntaxRepr t => t -> m a)
collectWithLog logLvl f = let
  collectors :: forall t. KnownSyntaxRepr t => t -> m a
  collectors = withKnownSyntaxRepr $ \repr syn -> case repr of
    SyntaxExprRepr -> logMsg logLvl (prettyShallowExpr syn) >> (f syn)
    SyntaxStmtRepr -> logMsg logLvl (prettyShallowStmt syn) >> (f syn)
    SyntaxLValRepr -> logMsg logLvl (T.pack (show syn)) >> (f syn)
    SyntaxTypeRepr -> logMsg logLvl (T.pack (show syn)) >> (f syn)
    SyntaxCallRepr -> unindentLog (logMsg logLvl ("Function Call: " <> T.pack (show syn)) >> (f syn))
  in collectors

-- Syntax traversal. Since the ASL syntax datatypes are monomorphic there is some complexity
-- in defining the standard traversal functions.

-- | Shallow monadic map of a syntax element
type SyntaxTraverser m = forall t. KnownSyntaxRepr t => t -> m t

-- | Shallow result from inspecting a syntax element
type SyntaxCollector w m = forall t. KnownSyntaxRepr t => t -> m w

-- | Shallow map of a syntax element
type SyntaxMap = forall t. KnownSyntaxRepr t => t -> t

-- | Recursive syntax collection. Results from individual syntax elements are collected in the given Monoid.
collectSyntax :: KnownSyntaxRepr t => Monoid w => MonadLog m => SyntaxCollector w m -> t -> m w
collectSyntax writes e = W.execWriterT (traverseSyntax (writeToTraverser writes) e)
  where
    writeToTraverser :: forall w m.
      Monoid w => MonadLog m => SyntaxCollector w m -> SyntaxTraverser (W.WriterT w m)
    writeToTraverser syntaxWrite =
      liftWrite syntaxWrite
      where
        liftWrite :: forall t. KnownSyntaxRepr t => (t -> m w) -> t -> W.WriterT w m t
        liftWrite f e' = MT.lift (f e') >>= (\w -> W.tell w >> return e')

-- | Recursive syntax mapping. The given map is applied top-down to each sub-element.
mapSyntax :: KnownSyntaxRepr t => SyntaxMap -> t -> t
mapSyntax smap t = I.runIdentity $ traverseSyntax (mapsToTraverser smap) t
  where
    mapsToTraverser :: SyntaxMap -> SyntaxTraverser I.Identity
    mapsToTraverser syntaxMap = (\t' -> return $ syntaxMap t')

-- | Recursive syntax traversal. Each sub-element is replaced by the result of the given monadic function.
traverseSyntax :: MonadLog m => KnownSyntaxRepr t => SyntaxTraverser m -> t -> m t
traverseSyntax col = withKnownSyntaxRepr $ \case
  SyntaxStmtRepr -> traverseStmt col
  SyntaxTypeRepr -> traverseType col
  SyntaxLValRepr -> traverseLVal col
  SyntaxExprRepr -> traverseExpr col
  SyntaxCallRepr -> traverseCall col


traverseCall :: MonadLog m
             => SyntaxTraverser m
             -> (AS.QualifiedIdentifier, [AS.Expr])
             -> m (AS.QualifiedIdentifier, [AS.Expr])
traverseCall cols (qIdent, argEs) =
  let
    f = traverseSyntax cols
  in cols (qIdent, argEs) >>= \(qIdent', argEs') ->
    (\argEs'' -> (qIdent', argEs'')) <$> (traverse f argEs')


getCall :: forall t
         . KnownSyntaxRepr t
        => t
        -> Maybe ((AS.QualifiedIdentifier, [AS.Expr]), (AS.QualifiedIdentifier, [AS.Expr]) -> t)
getCall = useKnownSyntaxRepr $ \syn -> \case
  SyntaxStmtRepr |
    AS.StmtCall qIdent argEs <- syn ->
      Just ((qIdent, argEs), uncurry AS.StmtCall)
  SyntaxExprRepr |
    AS.ExprCall qIdent argEs <- syn ->
      Just ((qIdent, argEs), uncurry AS.ExprCall)
  _ -> Nothing

-- A "call" syntactic element is either an ExprCall or a StmtCall
-- we (shallowly) traverse the identifier/arguments first
shallowTraverseCall :: forall m t. KnownSyntaxRepr t => MonadLog m => SyntaxTraverser m -> t -> m t
shallowTraverseCall tr t = case getCall t of
  Just (call, uncall) -> do
    call' <- tr call
    tr $ uncall call'
  Nothing -> tr t

traverseSlice :: forall m. MonadLog m => SyntaxTraverser m -> AS.Slice -> m AS.Slice
traverseSlice tr slice =
  let
    f :: forall t. KnownSyntaxRepr t => t -> m t
    f = traverseSyntax tr -- recursive traversal

  in case slice of
     AS.SliceSingle e -> AS.SliceSingle <$> (f e)
     AS.SliceOffset e e' -> App.liftA2 AS.SliceOffset (f e) (f e')
     AS.SliceRange e e' -> App.liftA2 AS.SliceRange (f e) (f e')

traverseExpr :: forall m. MonadLog m => SyntaxTraverser m -> AS.Expr -> m AS.Expr
traverseExpr tr expr =
  let
    f :: forall t. KnownSyntaxRepr t => t -> m t
    f = traverseSyntax tr -- recursive traversal

    foldSetElems slice = case slice of
      AS.SetEltSingle e -> AS.SetEltSingle <$> f e
      AS.SetEltRange e e' -> App.liftA2 AS.SetEltRange (f e) (f e')

  in shallowTraverseCall tr expr >>= \expr' -> indentLog $ case expr' of
    AS.ExprSlice e slices ->
      App.liftA2 AS.ExprSlice (f e) (traverse (traverseSlice tr) slices)

    AS.ExprIndex e slices ->
      App.liftA2 AS.ExprIndex (f e)
        (traverse (traverseSlice tr) slices)
    AS.ExprUnOp uop e -> (AS.ExprUnOp uop) <$> f e
    AS.ExprBinOp bop e e' -> App.liftA2 (AS.ExprBinOp bop) (f e) (f e')
    AS.ExprMembers e mems -> (\e' -> AS.ExprMembers e' mems) <$> f e
    AS.ExprInMask e mask -> (\e' -> AS.ExprInMask e' mask) <$> f e
    AS.ExprMemberBits e bits -> (\e' -> AS.ExprMemberBits e' bits) <$> f e
    AS.ExprCall ident es -> (\es' -> AS.ExprCall ident es') <$> traverse f es
    AS.ExprInSet e se -> App.liftA2 AS.ExprInSet (f e) $ traverse foldSetElems se
    AS.ExprTuple es -> AS.ExprTuple <$> traverse f es
    AS.ExprIf pes e -> App.liftA2 AS.ExprIf (indentLog $ traverse (\(x,y) -> App.liftA2 (,) (f x) (f y)) pes) (f e)
    AS.ExprMember e mem -> (\e' -> AS.ExprMember e' mem) <$> f e
    AS.ExprUnknown t -> (\t' -> AS.ExprUnknown t') <$> f t
    _ -> return expr'

traverseLVal :: forall m. MonadLog m => SyntaxTraverser m -> AS.LValExpr -> m AS.LValExpr
traverseLVal tr lval =
  let
    f :: forall t. KnownSyntaxRepr t => t -> m t
    f = traverseSyntax tr -- recursive traversal

  in tr lval >>= \lval' -> indentLog $ case lval' of
    AS.LValMember lv mem -> (\lv' -> AS.LValMember lv' mem) <$> f lv
    AS.LValMemberArray lv idx -> (\lv' -> AS.LValMemberArray lv' idx) <$> f lv
    AS.LValArrayIndex lv slices -> App.liftA2 AS.LValArrayIndex (f lv) $ traverse (traverseSlice tr) slices
    AS.LValSliceOf lv slices -> App.liftA2 AS.LValSliceOf (f lv) $ traverse (traverseSlice tr) slices
    AS.LValArray lvs -> AS.LValArray <$> traverse f lvs
    AS.LValTuple lvs -> AS.LValTuple <$> traverse f lvs
    AS.LValMemberBits lv bits -> (\lv' -> AS.LValMemberBits lv' bits) <$> f lv
    AS.LValSlice lvs -> AS.LValSlice <$> traverse f lvs
    _ -> return lval'

traverseType :: forall m. MonadLog m => SyntaxTraverser m -> AS.Type -> m AS.Type
traverseType tr t =
  let
    f :: forall t. KnownSyntaxRepr t => t -> m t
    f = traverseSyntax tr -- recursive traversal

    foldField field = case field of
      AS.RegField i slices -> (\slices' -> AS.RegField i slices') <$>
        traverse (traverseSlice tr) slices

    foldIxType ix = case ix of
      AS.IxTypeRange e e' -> App.liftA2 AS.IxTypeRange (f e) (f e')
      _ -> return ix

  in tr t >>= \t' -> indentLog $ case t' of
    AS.TypeFun i e -> (\e' -> AS.TypeFun i e') <$> f e
    AS.TypeOf e -> AS.TypeOf <$> f e
    AS.TypeReg i fs -> (\fs' -> AS.TypeReg i fs') <$> traverse foldField fs
    AS.TypeArray ty ixt -> App.liftA2 AS.TypeArray (f ty) (foldIxType ixt)
    _ -> return t'

traverseStmt :: forall m. MonadLog m => SyntaxTraverser m -> AS.Stmt -> m AS.Stmt
traverseStmt tr stmt =
  let
    f :: forall t. KnownSyntaxRepr t => t -> m t
    f = traverseSyntax tr -- recursive traversal

    h' (ident, ty) = (\ty' -> (ident, ty')) <$> (f ty)

    foldCases cases = case cases of
      AS.CaseWhen pats me stmts ->
        App.liftA2 (\me' stmts' -> AS.CaseWhen pats me' stmts')
          (traverse f me)
          (traverse f stmts)
      AS.CaseOtherwise stmts -> AS.CaseOtherwise <$> traverse f stmts

    foldCatches catches = case catches of
      AS.CatchWhen e stmts ->
        App.liftA2 AS.CatchWhen (f e) $ traverse f stmts
      AS.CatchOtherwise stmts -> AS.CatchOtherwise <$> traverse f stmts

  in shallowTraverseCall tr stmt >>= \stmt' -> indentLog $ case stmt' of
    AS.StmtVarsDecl ty idents -> (\ty' -> AS.StmtVarsDecl ty' idents) <$> f ty
    AS.StmtVarDeclInit decl e -> App.liftA2 AS.StmtVarDeclInit (h' decl) (f e)
    AS.StmtConstDecl decl e -> App.liftA2 AS.StmtConstDecl (h' decl) (f e)
    AS.StmtAssign lv e ->  App.liftA2 AS.StmtAssign (f lv) (f e)
    AS.StmtCall ident es -> (\es' -> AS.StmtCall ident es') <$> traverse f es
    AS.StmtReturn me -> (\me' -> AS.StmtReturn me') <$> traverse f me
    AS.StmtAssert e -> AS.StmtAssert <$> f e
    AS.StmtIf tests melse ->
      App.liftA2 AS.StmtIf
        (traverse (\(e, stmts) -> App.liftA2 (,) (f e) (indentLog $ traverse f stmts)) tests)
        (indentLog $ traverse (\stmt'' -> traverse f stmt'') melse)
    AS.StmtCase e alts -> App.liftA2 AS.StmtCase (f e) (traverse foldCases alts)
    AS.StmtFor ident rng stmts -> App.liftA2 (\rng' stmts' -> AS.StmtFor ident rng' stmts')
      (App.liftA2 (,) (f $ fst rng) (f $ snd rng))
      (indentLog $ traverse f stmts)
    AS.StmtWhile e stmts -> App.liftA2 AS.StmtWhile (f e) (indentLog $ traverse f stmts)
    AS.StmtRepeat stmts e -> App.liftA2 AS.StmtRepeat (indentLog $ traverse f stmts) (f e)
    AS.StmtSeeExpr e -> AS.StmtSeeExpr <$> f e
    AS.StmtTry stmts ident alts -> App.liftA2 (\stmts' alts' -> AS.StmtTry stmts' ident alts')
      (indentLog $ traverse f stmts)
      (indentLog $ traverse foldCatches alts)
    _ -> return stmt'

prettyShallowStmt :: AS.Stmt -> T.Text
prettyShallowStmt stmt = case stmt of
  AS.StmtIf _ _ -> "StmtIf: "
  AS.StmtFor var range _ -> "StmtFor: " <> T.pack (show var) <> T.pack (show range)
  AS.StmtRepeat _ _ -> "StmtRepeat: "
  AS.StmtWhile _ _ -> "StmtWhile: "
  _ -> T.pack $ show stmt


prettyShallowExpr :: AS.Expr -> T.Text
prettyShallowExpr expr = case expr of
  AS.ExprIf _ _ -> "ExprIf: "
  _ -> T.pack $ show expr

getterText :: Bool -> T.Text
getterText withArgs = if withArgs then "GETTER_" else "BAREGETTER_"

mkGetterName :: Bool -> AS.QualifiedIdentifier -> AS.QualifiedIdentifier
mkGetterName withArgs = do
  mapInnerName (\s -> getterText withArgs <> s)

setterText :: Bool -> T.Text
setterText withArgs = if withArgs then "SETTER_" else "BARESETTER_"

mkSetterName :: Bool -> AS.QualifiedIdentifier -> AS.QualifiedIdentifier
mkSetterName withArgs = mapInnerName (\s -> setterText withArgs <> s)

-- | Make a function name given its ASL name and arity.
mkFunctionName :: AS.QualifiedIdentifier -> Int -> T.Text
mkFunctionName name numArgs = collapseQualID name <> T.pack "_" <> T.pack (show numArgs)


collapseQualID :: AS.QualifiedIdentifier -> T.Text
collapseQualID (AS.QualifiedIdentifier AS.ArchQualAArch64 name) = "AArch64_" <> name
collapseQualID (AS.QualifiedIdentifier AS.ArchQualAArch32 name) = "AArch32_" <> name
collapseQualID (AS.QualifiedIdentifier _ name) = name

mapInnerName :: (T.Text -> T.Text) -> AS.QualifiedIdentifier -> AS.QualifiedIdentifier
mapInnerName f (AS.QualifiedIdentifier q name) = AS.QualifiedIdentifier q (f name)
