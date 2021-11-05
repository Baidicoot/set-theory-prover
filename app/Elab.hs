{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
module Elab where

import Kernel
import ParserTypes

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Map as M

{- elaboration of parse trees into Kernel.Types structures -}

data NameOrigin
    = Local
    | Global

data NameLevel
    = Sort
    | Obj
    | Prf
    deriving(Eq)

type Namespace = M.Map Name (Name, NameOrigin, NameLevel)
type ElabCtx = Namespace

lookupIdent :: Name -> NameLevel -> Elaborator (Name, NameOrigin)
lookupIdent n l = do
    x <- fmap (M.lookup n) ask
    case x of
        Just (n', o, l') | l == l' -> pure
        Just (_, _, l') -> throwError (NamespaceError n l l')

type Elaborator = ExceptT ParseError (ReaderT ElabCtx (State [Name]))

fresh :: Elaborator Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

freshen :: Name -> Elaborator a -> Elaborator (Name, a)
freshen n f = do
    n' <- fresh
    fmap (,n') (local (M.insert n (n', Local)) f)

elabSort :: SExpr -> Elaborator Monotype
elabSort (SExpr "func" [x,y]) = liftM2 Arr (elabSort x) (elabSort y)
elabSort (SExpr "prop" []) = pure Prop
elabSort x = do
    (n, k) <- elabBound x =<< sortNamespace
    case k of
        Local -> pure (TyVar n)
        Global -> pure (ConstTy n)
elabSort x = throwError (ElabError x "monotype")

elabBound :: SExpr -> Elaborator (Name, NameOrigin)
elabBound x@(STok (Tok Ident n)) = do
    (i,o) <- lookupIdent Sort n
    case o of
        Local -> pure (TyVar i)
        Global -> pure (ConstTy i)
elabBound x _ = throwError (ElabError x "identifier")

elabIdent :: SExpr -> Elaborator Name
elabIdent (STok (Tok Ident n)) = pure n
elabIdent x = throwError (ElabError x "identifier")

elabTerm :: SExpr -> Elaborator Term
elabTerm (SExpr "lam" [x,y]) = do
    n <- elabIdent x
    (n', y') <- freshen n y
    pure (Lam n' y')
