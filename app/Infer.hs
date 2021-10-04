{-# LANGUAGE FlexibleInstances #-}
module Infer where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Logic

{-
Infer.hs - INFERENCE FOR THE OBJECT LANGUAGE
============================================
Basically just Hindley-Milner.
Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
-}

type Subst = M.Map Name Monotype
type TypingCtx = M.Map Name Polytype

names :: [Name]
names = [T.pack (v:show n) | v <- ['A'..'Z'], n <- [0..]]

data TypeError
    = InfiniteType Name Monotype
    | UnificationFail Monotype Monotype
    | NotInContext Name

type Infer = ExceptT TypeError (State [Name])

fresh :: Infer Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

class Substitutable a where
    subst :: Subst -> a -> a
    free :: a -> S.Set Name

occurs :: Substitutable a => Name -> a -> Bool
occurs n = S.member n . free

instance Substitutable Monotype where
    subst s (Arr a b) = Arr (subst s a) (subst s b)
    subst s (TyVar n) = case M.lookup n s of
        Nothing -> TyVar n
        Just t -> t
    subst _ t = t
    
    free (Arr a b) = free a `S.union` free b
    free (TyVar n) = S.singleton n
    free _ = S.empty

instance Substitutable Polytype where
    subst s (Polytype v t) =
        Polytype v (subst (M.filterWithKey (\k _ -> S.member k (M.keysSet s)) s) t)
    free (Polytype v t) = free t `S.difference` v

instance Substitutable TypingCtx where
    subst s ctx = fmap (subst s) ctx
    free ctx = S.unions (M.elems $ fmap free ctx)

instance Substitutable Term where
    subst s (Lam v t e) = Lam v (subst s t) (subst s e)
    subst s (Let v t e) = Let v (subst s t) (subst s e)
    subst s (App f x) = App (subst s f) (subst s x)
    subst s (Imp a b) = Imp (subst s a) (subst s b)
    subst s (Forall v t e) = Forall v (subst s t) (subst s e)
    subst _ x = x

    free (Lam _ t e) = free t `S.union` free e
    free (Let _ a b) = free a `S.union` free b
    free (App a b) = free a `S.union` free b
    free (Imp a b) = free a `S.union` free b
    free (Forall _ t e) = free t `S.union` free e
    free _ = S.empty

instantiate :: Polytype -> Infer Monotype
instantiate (Polytype v t) = do
    s <- M.fromList <$> mapM (\n -> ((,) n . TyVar) <$> fresh) (S.toList v)
    pure (subst s t)

generalize :: TypingCtx -> Monotype -> Polytype
generalize ctx t = Polytype (free t `S.difference` M.keysSet ctx) t

composeSubst :: Subst -> Subst -> Subst
composeSubst f g = fmap (subst f) g `M.union` f

bind :: Name -> Monotype -> Infer Subst
bind a t
    | t == TyVar a = pure M.empty
    | occurs a t = throwError $ InfiniteType a t
    | otherwise = pure $ M.singleton a t

unify :: Monotype -> Monotype -> Infer Subst
unify (Arr a b) (Arr c d) = do
    f <- unify a c
    g <- unify b d
    pure (composeSubst g f)
unify (TyVar a) b = bind a b
unify a (TyVar b) = bind b a
unify x y | x == y = pure M.empty
unify x y = throwError (UnificationFail x y)

infer :: TypingCtx -> Term -> Infer (Subst, Monotype)
infer ctx (Lam v tv m) = do
    (s, t) <- infer (M.insert v (Polytype S.empty tv) ctx) m
    pure (s, Arr (subst s tv) t)
infer ctx (Var v) = case M.lookup v ctx of
    Just s -> do
        t <- instantiate s
        pure (M.empty, t)
    Nothing -> throwError (NotInContext v)
infer ctx (Let v n m) = do
    (sn, tn) <- infer ctx n
    (sm, tm) <- infer (M.insert v (generalize (subst sn ctx) tn) ctx) m
    pure (composeSubst sn sm, tm)
infer ctx (App f x) = do
    tv <- fmap TyVar fresh
    (sx, tx) <- infer ctx x
    (sf, tf) <- infer ctx f
    s <- unify tf (Arr tx tv)
    pure (composeSubst (composeSubst s sf) sx, subst s tv)
infer ctx (Imp a b) = do
    (sa, ta) <- infer ctx a
    sau <- unify ta Prop
    (sb, tb) <- infer ctx b
    sbu <- unify tb Prop
    pure (composeSubst (composeSubst sa sau) (composeSubst sb sbu), Prop)
infer ctx (Forall v tv m) = do
    (s, t) <- infer (M.insert v (Polytype S.empty tv) ctx) m
    su <- unify t Prop
    pure (composeSubst s su, Prop)