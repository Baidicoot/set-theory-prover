{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module Elab where

import Kernel hiding (fresh,Name)
import ParserTypes

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Data.Map as M
import qualified Data.Set as S

{- elaboration of parse trees into Kernel.Types structures -}

lookupIdent :: Name -> NameLevel -> Elaborator (Name, NameOrigin)
lookupIdent n l = do
    x <- asks (M.lookup n)
    case x of
        Just (n', o, l') | l == l' -> pure (n', o)
        Just (_, _, l') -> throwError (NamespaceError n l l')
        Nothing -> throwError (ScopeError n)

-- writes contexts for each hole
type Elaborator = ExceptT ParseError (WriterT [ElabCtx] (ReaderT ElabCtx (State [Name])))

fresh :: Elaborator Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

freshen :: Name -> NameOrigin -> NameLevel -> Elaborator a -> Elaborator (Name, a)
freshen n o l f = do
    n' <- fresh
    fmap (n',) (local (M.insert n (n', o, l)) f)

elabSort :: SExpr -> Elaborator Monotype
elabSort (SExpr "func" [x,y]) = liftM2 Arr (elabSort x) (elabSort y)
elabSort (SExpr "prop" []) = pure Prop
elabSort x = do
    (n, k) <- elabBound x Sort
    case k of
        Implicit -> pure (TyVar n)
        Local -> pure (TyVar n)
        Global -> pure (ConstTy n)

unboundIdents :: SExpr -> Elaborator [Name]
unboundIdents (SExpr _ xs) = concat <$> mapM unboundIdents xs
unboundIdents (STok (Tok Ident n)) = do
    x <- asks (M.lookup n)
    case x of
      Nothing -> pure [n]
      Just _ -> pure []
unboundIdents _ = pure []

elabMonotype :: SExpr -> Elaborator Monotype
elabMonotype x = do
    fvs <- unboundIdents x
    foldr (\n -> fmap snd . freshen n Implicit Sort) (elabSort x) fvs

elabPolytype :: SExpr -> Elaborator Polytype
elabPolytype x = do
    fvs <- unboundIdents x
    fmap (Polytype (S.fromList fvs)) $ foldr (\n -> fmap snd . freshen n Implicit Sort) (elabSort x) fvs

elabBound :: SExpr -> NameLevel -> Elaborator (Name, NameOrigin)
elabBound x@(STok (Tok Ident n)) = lookupIdent n
elabBound x = const (throwError (ElabError x "expected bound identifier"))

elabIdent :: SExpr -> Elaborator Name
elabIdent (STok (Tok Ident n)) = pure n
elabIdent x = throwError (ElabError x "expected identifier")

elabProp :: SExpr -> Elaborator Term
elabProp x = do
    fvs <- unboundIdents x
    foldr (\n -> fmap snd . freshen n Implicit Sort) (elabTerm x) fvs

elabTerm :: SExpr -> Elaborator Term
elabTerm (SExpr "lam" [x,y]) = do
    n <- elabIdent x
    (n', y') <- freshen n Local Obj (elabTerm y)
    pure (Lam n' y')
elabTerm (SExpr "let" [x,y,z]) = do
    n <- elabIdent x
    y' <- elabTerm y
    (n', z') <- freshen n Local Obj (elabTerm z)
    pure (Let n' y' z')
elabTerm (SExpr "app" [x,y]) = liftM2 App (elabTerm x) (elabTerm y)
elabTerm (SExpr "forall" [x,y,z]) = do
    n <- elabIdent x
    y' <- elabMonotype y
    (n', z') <- freshen n Local Obj (elabTerm z)
    pure (Forall n' y' z')
elabTerm (SExpr "imp" [x,y]) = liftM2 Imp (elabTerm x) (elabTerm y)
elabTerm (SExpr "hole" []) = MetaVar <$> fresh
elabTerm x = do
    (n,o) <- elabBound x Obj
    case o of
      Local -> pure (Var n)
      Global -> pure (Var n)
      Implicit -> pure (MetaVar n)

elabProof :: SExpr -> Elaborator Proof
elabProof (SExpr "introThm" [x,y,z]) = do
    n <- elabIdent x
    y' <- elabTerm y
    (n', z') <- freshen n Local Prf (elabProof z)
    pure (IntroThm n' y' z')
elabProof (SExpr "introObj" [x,y,z]) = do
    n <- elabIdent x
    y' <- elabSort y
    (n', z') <- freshen n Local Prf (elabProof z)
    pure (IntroObj n' y' z')
elabProof (SExpr "modPon" [x,y]) = do
    x' <- error (show [x,y]) >> elabProof x
    y' <- elabProof y
    pure (ModPon x' y')
elabProof (SExpr "uniElim" [x,y]) = do
    x' <- elabProof x
    y' <- elabProp y
    pure (UniElim x' y')
elabProof (SExpr "hole" []) = do
    ctx <- ask
    tell [ctx]
    pure Hole
elabProof x = do
    (n,o) <- elabBound x Prf
    case o of
        Local -> pure (Axiom n)
        Implicit -> error "UNREACHABLE"
        Global -> pure (Axiom n)

elabNotation :: SExpr -> Elaborator (Name, [NotationBinding])
elabNotation (SExpr t xs) = (t,) <$> mapM elabNotationBinding xs
elabNotation x = throwError (ElabError x "expected notation")

elabNotationBinding :: SExpr -> Elaborator NotationBinding
elabNotationBinding (SExpr s [x]) = do
    n <- elabIdent x
    pure (BindNonterminal s n)
elabNotationBinding (STok t) = pure (ExactToken t)
elabNotationBinding x = throwError (ElabError x "expected nonterminal or token")

runElaborator :: [Name] -> ElabCtx -> Elaborator a -> ((Either ParseError a, [ElabCtx]), [Name])
runElaborator n c = flip runState n . flip runReaderT c . runWriterT . runExceptT