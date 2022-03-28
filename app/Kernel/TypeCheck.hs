{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module Kernel.TypeCheck (inferObj, unifyTyp, checkObj, generalize) where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trace
import Control.Monad.Reader

import Kernel.Types
import Kernel.Subst

{-
Infer.hs - INFERENCE FOR THE OBJECT LANGUAGE
============================================
Basically just Hindley-Milner.
Implemented as Algorithm W (https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#Algorithm_W)

maybe use ~sane~ non-haskellic variable naming scheme
-}

occurs :: Substitutable Monotype a => Name -> a -> Bool
occurs n = S.member n . free @Monotype

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

unifyTyp :: Monotype -> Monotype -> Infer TypeSubst
unifyTyp (Arr a b) (Arr c d) = do
    f <- unifyTyp a c
    g <- unifyTyp (subst f b) (subst f d)
    pure (g<+f)
unifyTyp (TyVar a) b = bind a b
unifyTyp a (TyVar b) = bind b a
unifyTyp x y | x == y = pure M.empty
unifyTyp x y = throwError (MonotypeUnificationFail x y)

inferObj :: TypeCtx -> Term -> Infer (TypeSubst, Monotype)
inferObj ctx t = traceError (InferringTerm t) (inferObj' ctx t)
    where
    inferObj' ctx (Lam x e) = do
        t <- fmap TyVar fresh
        (s, t') <- inferObj (M.insert x (Polytype S.empty t) ctx) e
        pure (s, Arr (subst s t) t')
    inferObj' ctx (Var x) =
        case M.lookup x ctx of
            Just s -> do
                t <- instantiate s
                pure (M.empty, t)
            Nothing -> throwError (NotInContext x)
    inferObj' ctx (MetaVar x) = do
        (_,ms) <- get
        case M.lookup x ms of
            Just t -> pure (M.empty, t)
            Nothing -> do
                t <- discoverMetaVar x
                pure (M.empty, t)
    inferObj' ctx (Let x e0 e1) = do
        (s0, t) <- inferObj ctx e0
        let t' = generalize (subst s0 ctx) t
        (s1, t1) <- inferObj (M.insert x t' (subst s0 ctx)) (subst s0 e1)
        pure (s1<+s0, t1)
    inferObj' ctx (App e0 e1) = do
        (s0, t0) <- inferObj ctx e0
        (s1, t1) <- inferObj (subst s0 ctx) (subst s0 e1)
        t' <- fmap TyVar fresh
        s2 <- unifyTyp (subst s1 t0) (Arr t1 t')
        pure (s2<+s1<+s0, subst s2 t')
    inferObj' ctx (Imp e0 e1) = do
        (s0, t0) <- inferObj ctx e0
        s0' <- unifyTyp t0 Prop
        (s1, t1) <- inferObj (subst (s0<+s0') ctx) (subst (s0<+s0') e1)
        s1' <- unifyTyp (subst (s0<+s0') t1) Prop
        pure (s1<+s1'<+s0<+s0', Prop)
    inferObj' ctx (Forall x t e) = do
        (s, t') <- inferObj (M.insert x (Polytype S.empty t) ctx) e
        s' <- unifyTyp t' Prop
        pure (s<+s', Prop)

checkObj :: TypeCtx -> Term -> Monotype -> Infer (TypeSubst, Term)
checkObj ctx e t = traceError (CheckingTerm e t) $ do
    (s0,t') <- inferObj ctx e
    s1 <- unifyTyp (subst s0 t) t'
    pure (s1<+s0, subst (s1<+s0) e)