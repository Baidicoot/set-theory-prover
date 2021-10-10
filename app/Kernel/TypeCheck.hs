{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Kernel.TypeCheck where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Kernel.Types
import Kernel.Subst

{-
Infer.hs - INFERENCE FOR THE OBJECT LANGUAGE
============================================
Basically just Hindley-Milner.
Adapted from http://dev.stephendiehl.com/fun/006_hindley_milner.html
-}

type TypingCtx = M.Map Name Polytype

occurs :: Substitutable Monotype a => Name -> a -> Bool
occurs n = S.member n . free @Monotype

instance Substitutable Monotype Monotype where
    subst s (Arr a b) = Arr (subst s a) (subst s b)
    subst s (TyVar n) = case M.lookup n s of
        Nothing -> TyVar n
        Just t -> t
    subst _ t = t
    
    free (Arr a b) = free @Monotype a `S.union` free @Monotype b
    free (TyVar n) = S.singleton n
    free _ = S.empty

instance Substitutable Monotype Polytype where
    subst s (Polytype v t) =
        Polytype v (subst (M.filterWithKey (\k _ -> S.member k (M.keysSet s)) s) t)
    free (Polytype v t) = free @Monotype t `S.difference` v

instance Substitutable Monotype TypingCtx where
    subst s ctx = fmap (subst s) ctx
    free ctx = S.unions (M.elems $ fmap (free @Monotype) ctx)

instance Substitutable Monotype Term where
    subst s (Lam v t e) = Lam v (subst s t) (subst s e)
    subst s (Let v t e) = Let v (subst s t) (subst s e)
    subst s (App f x) = App (subst s f) (subst s x)
    subst s (Imp a b) = Imp (subst s a) (subst s b)
    subst s (Forall v t e) = Forall v (subst s t) (subst s e)
    subst _ x = x

    free (Lam _ t e) = free @Monotype t `S.union` free @Monotype e
    free (Let _ a b) = free @Monotype a `S.union` free @Monotype b
    free (App a b) = free @Monotype a `S.union` free @Monotype b
    free (Imp a b) = free @Monotype a `S.union` free @Monotype b
    free (Forall _ t e) = free @Monotype t `S.union` free @Monotype e
    free _ = S.empty

instantiate :: Polytype -> Infer Monotype
instantiate (Polytype v t) = do
    s <- M.fromList <$> mapM (\n -> ((,) n . TyVar) <$> fresh) (S.toList v)
    pure (subst s t)

generalize :: TypingCtx -> Monotype -> Polytype
generalize ctx t = Polytype (free @Monotype t `S.difference` M.keysSet ctx) t

bind :: Name -> Monotype -> Infer TypeSubst
bind a t
    | t == TyVar a = pure M.empty
    | occurs a t = throwError $ InfiniteType a t
    | otherwise = pure $ M.singleton a t

unify :: Monotype -> Monotype -> Infer TypeSubst
unify (Arr a b) (Arr c d) = do
    f <- unify a c
    g <- unify b d
    pure (composeSubst g f)
unify (TyVar a) b = bind a b
unify a (TyVar b) = bind b a
unify x y | x == y = pure M.empty
unify x y = throwError (TypeUnificationFail x y)

infer :: TypingCtx -> Term -> Infer (TypeSubst, Monotype, MetaVarTypes)
infer ctx (Lam v tv m) = do
    (s, t) <- infer (M.insert v (Polytype S.empty tv) ctx) m
    pure (s, Arr (subst s tv) t)
infer ctx (Var v) = case M.lookup v ctx of
    Just s -> do
        t <- instantiate s
        pure (M.empty, t)
    Nothing -> throwError (NotInContext v)
infer ctx (MetaVar v) = do
    {- maybe add MetaVarTypes to state? -}
infer ctx (Let v n m) = do
    (sn, tn) <- infer ctx n
    (sm, tm) <- infer (M.insert v (generalize (subst sn ctx) tn) ctx) m
    pure (composeSubst sn sm, tm)
infer ctx (App f x) = do
    tv <- fmap TyVar fresh
    (sx, tx) <- infer ctx x
    (sf, tf) <- infer ctx (subst sx f)
    sa <- unify tf (Arr (subst sf tx) tv)
    pure (composeSubst (composeSubst sa sf) sx, subst s tv)
infer ctx (Imp a b) = do
    (sa, ta) <- infer ctx a
    sau <- unify ta Prop
    (sb, tb) <- infer ctx (subst sa b)
    sbu <- unify (subst sa tb) Prop
    pure (composeSubst (composeSubst sb sbu) (composeSubst sa sau), Prop)
infer ctx (Forall v tv m) = do
    (s, t) <- infer (M.insert v (Polytype S.empty tv) ctx) m
    su <- unify t Prop
    pure (composeSubst s su, Prop)