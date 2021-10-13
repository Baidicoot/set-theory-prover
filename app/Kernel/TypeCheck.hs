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
Implemented as Algorithm W (https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_W)

maybe make ~sane~ non-haskellic variable naming scheme
-}

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

generalize :: TypeCtx -> Monotype -> Polytype
generalize ctx t = Polytype (free @Monotype t `S.difference` M.keysSet ctx) t

bind :: Name -> Monotype -> Infer TypeSubst
bind a t
    | t == TyVar a = pure M.empty
    | occurs a t = throwError $ InfiniteType a t
    | otherwise = pure $ M.singleton a t

unify :: Monotype -> Monotype -> Infer TypeSubst
unify (Arr a b) (Arr c d) = do
    f <- unify a c
    g <- unify (subst f b) (subst f g)
    pure (g<:f)
unify (TyVar a) b = bind a b
unify a (TyVar b) = bind b a
unify x y | x == y = pure M.empty
unify x y = throwError (TypeUnificationFail x y)

{- MIGHT NEED TO SUBSTITUTE INTO ANNOTATIONS IN FORALL? -}
infer :: Term -> Infer (TypeSubst, Monotype)
infer (Lam x e) = do
    t <- fmap TyVar fresh
    (s, t') <- local (M.insert v (Polytype S.empty t)) (infer e)
    pure (s, Arr (subst s t) t')
infer (Var x) = do
    ctx <- ask
    case M.lookup x ctx of
        Just s -> do
            t <- instantiate s
            pure (M.empty, t)
        Nothing -> throwError (NotInContext x)
infer (Const x) = do
    ctx <- ask
    case M.lookup x ctx of
        Just s -> do
            t <- instantiate s
            pure (M.empty, t)
        Nothing -> throwError (UnknownConst x)
infer (MetaVar x) = do
    (_,ms) <- get
    case M.lookup x ctx of
        Just t -> pure (M.empty, t)
        Nothing -> do
            t <- discoverMetaVar x
            pure (M.empty, t)
infer (Let x e0 e1) = do
    (s0, t) <- infer e0
    ctx <- ask
    (s1, t1) <- local (M.insert x (generalize (subst s0 ctx) t)) (infer e1)
    pure (s1<:s0, t1)
infer (App e0 e1) = do
    (s0, t0) <- infer e0
    (s1, t1) <- local (subst s0) (infer e1)
    t' <- fmap TyVar fresh
    s2 <- unify (subst s1 t0) (Arr t1 t')
    pure (s2<:s1<:s0, subst s2 t')
infer (Imp e0 e1) = do
    (s0, t0) <- infer e0
    s0' <- unify t0 Prop
    (s1, t1) <- infer e1
    s1' <- unify (subst s0 t1) Prop
    pure (s1<:s1'<:s0<:s0', Prop)
infer (Forall x t e) = do
    (s, t') <- local (M.insert x (Polytype S.empty t)) (infer e)
    s' <- unify t' Prop
    pure (s<:s', Prop)