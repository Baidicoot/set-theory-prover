{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Kernel.Subst where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Writer

import Kernel.Types

type Subst = M.Map Name

type TermSubst = Subst Term
type TypeSubst = Subst Monotype

{- LEFT-BIASED COMPOSITION -}
composeSubst :: Substitutable a a => Subst a -> Subst a -> Subst a
composeSubst f g = fmap (subst f) g `M.union` f

(<+) :: Substitutable a a => Subst a -> Subst a -> Subst a
(<+) = composeSubst

infixr 0 <+

class Substitutable a b where
    subst :: Subst a -> b -> b
    free :: b -> S.Set Name

instance Substitutable a b => Substitutable a (Maybe b) where
    subst s (Just b) = Just (subst s b)
    subst _ Nothing = Nothing

    free (Just b) = free @a b
    free Nothing = S.empty

instance (Foldable t, Functor t, Substitutable a b) => Substitutable a (t b) where
    subst s m = fmap (subst s) m
    free m = S.unions (fmap (free @a) m)

class Container a b where
    mapC :: Monad m => (b -> m b) -> a -> m a

instance Traversable f => Container (f a) a where
    mapC = traverse

instance Container x x where
    mapC = id

instance Container Proof Term where
    mapC f (ModPon a b) = liftM2 ModPon (mapC f a) (mapC f b)
    mapC f (UniElim p t) = liftM2 UniElim (mapC f p) (f t)
    mapC f (IntroObj n t p) = fmap (IntroObj n t) (mapC f p)
    mapC f (IntroThm n t p) = liftM2 (IntroThm n) (f t) (mapC f p)
    mapC _ x = pure x

instance Container Term Monotype where
    mapC f (Lam n e) = fmap (Lam n) (mapC f e)
    mapC f (Let n e0 e1) = liftM2 (Let n) (mapC f e0) (mapC f e1)
    mapC f (App e0 e1) = liftM2 App (mapC f e0) (mapC f e1)
    mapC f (Imp e0 e1) = liftM2 Imp (mapC f e0) (mapC f e1)
    mapC f (Forall n t e) = liftM2 (Forall n) (f t) (mapC f e)
    mapC _ x = pure x

instance Substitutable Monotype Monotype where
    subst s (Arr a b) = Arr (subst s a) (subst s b)
    subst s (TyVar n) = case M.lookup n s of
        Nothing -> TyVar n
        Just t -> t
    subst _ t = t
    
    free (Arr a b) = free @Monotype a `S.union` free @Monotype b
    free (TyVar n) = S.singleton n
    free _ = S.empty

instance Substitutable Term Term where
    subst s (Lam n t) = Lam n (subst s t)
    subst s (Let n t0 t1) = Let n (subst s t0) (subst s t1)
    subst s (App t0 t1) = App (subst s t0) (subst s t1)
    subst s (Imp t0 t1) = Imp (subst s t0) (subst s t1)
    subst s (Forall n m t) = Forall n m (subst s t)
    subst s (Var n) = case M.lookup n s of
        Just t -> t
        Nothing -> Var n
    subst s x = x

    free (Var n) = S.singleton n
    free (Lam n e) = S.delete n (free @Term e)
    free (Let n e0 e1) = free @Term e0 `S.union` S.delete n (free @Term e1)
    free (App e0 e1) = free @Term e0 `S.union` free @Term e1
    free (Imp e0 e1) = free @Term e0 `S.union` free @Term e1
    free (Forall n _ e) = S.delete n (free @Term e)
    free _ = S.empty

{-
unfortunately, (Container a b,Container b c) => Container a c
and (Container a c,Substitutable b c) => Substitutable b a
require UndecidableInstances, so they have to be done manually:
-}

instance Container Proof Monotype where
    mapC = mapC . (mapC :: Monad m => (Monotype -> m Monotype) -> Term -> m Term)

instance Substitutable Monotype Term where
    subst s = runIdentity .
        (mapC :: (Monotype -> Identity Monotype) -> Term -> Identity Term) (Identity . subst s)
    free = execWriter .
        (mapC :: (Monotype -> Writer (S.Set Name) Monotype) -> Term -> Writer (S.Set Name) Term)
        (\c -> tell (free @Monotype c) >> pure c)

instance Substitutable Monotype Proof where
    subst s = runIdentity .
        (mapC :: (Monotype -> Identity Monotype) -> Proof -> Identity Proof) (Identity . subst s)
    free = execWriter .
        (mapC :: (Monotype -> Writer (S.Set Name) Monotype) -> Proof -> Writer (S.Set Name) Proof)
        (\c -> tell (free @Monotype c) >> pure c)

class Renamable a where
    rename :: a -> Infer a
    replace :: Name -> Name -> a -> a

instance Renamable Term where
    rename (Lam n t) = do
        x <- fresh
        Lam x . replace n x <$> rename t
    rename (Let n t0 t1) = do
        x <- fresh
        liftM2 (Let x) (rename t0) (replace n x <$> rename t1)
    rename (App t0 t1) = liftM2 App (rename t0) (rename t1)
    rename (Imp t0 t1) = liftM2 Imp (rename t0) (rename t1)
    rename (Forall n m t) = do
        x <- fresh
        Forall x m . replace n x <$> rename t
    rename x = pure x

    replace n x (Lam m t) = Lam m (replace n x t)
    replace n x (Let m t0 t1) = Let m (replace n x t0) (replace n x t1)
    replace n x (App t0 t1) = App (replace n x t0) (replace n x t1)
    replace n x (Imp t0 t1) = Imp (replace n x t0) (replace n x t1)
    replace n x (Forall m s t) = Forall m s (replace n x t)
    replace n x (Var m) | m == n = Var x
    replace _ _ x = x

{-
data SubstRenaming a b = SubstRenaming
    { substRenaming :: Subst a -> b -> Infer b
    , locations :: a -> S.Set Name
    }

{- LEFT-BIASED COMPOSITION -}
composeRenamingSubst :: SubstRenaming a a -> Subst a -> Subst a -> Infer (Subst a)
composeRenamingSubst (SubstRenaming subst _) f g = M.union f <$> traverse (subst f) g
-}

substVars :: Subst Term -> Term -> Infer Term
substVars s (Lam n t) = Lam n <$> substVars s t
substVars s (Let n t0 t1) = liftM2 (Let n) (substVars s t0) (substVars s t1)
substVars s (App t0 t1) = liftM2 App (substVars s t0) (substVars s t1)
substVars s (Imp t0 t1) = liftM2 Imp (substVars s t0) (substVars s t1)
substVars s (Forall n m t) = Forall n m <$> substVars s t
substVars s (Var n) = case M.lookup n s of
    Just t -> rename t
    Nothing -> pure (Var n)
substVars s x = pure x

substMeta :: Subst Term -> Term -> Infer Term
substMeta s (Lam n t) = Lam n <$> substMeta s t
substMeta s (Let n t0 t1) = liftM2 (Let n) (substMeta s t0) (substMeta s t1)
substMeta s (App t0 t1) = liftM2 App (substMeta s t0) (substMeta s t1)
substMeta s (Imp t0 t1) = liftM2 Imp (substMeta s t0) (substMeta s t1)
substMeta s (Forall n m t) = Forall n m <$> substMeta s t
substMeta s (MetaVar n) = case M.lookup n s of
    Just t -> rename t
    Nothing -> pure (MetaVar n)
substMeta s x = pure x

freeVars :: Term -> S.Set Name
freeVars (Lam n t) = S.delete n (freeVars t)
freeVars (Let n t0 t1) = S.delete n (freeVars t0 `S.union` freeVars t1)
freeVars (App t0 t1) = freeVars t0 `S.union` freeVars t1
freeVars (Imp t0 t1) = freeVars t0 `S.union` freeVars t1
freeVars (Forall n _ t) = S.delete n (freeVars t)
freeVars (Var n) = S.singleton n
freeVars _ = S.empty

metaVars :: Term -> S.Set Name
metaVars (Lam _ t) = metaVars t
metaVars (Let _ t0 t1) = metaVars t0 `S.union` metaVars t1
metaVars (App t0 t1) = metaVars t0 `S.union` metaVars t1
metaVars (Imp t0 t1) = metaVars t0 `S.union` metaVars t1
metaVars (Forall _ _ t) = metaVars t
metaVars (MetaVar n) = S.singleton n
metaVars _ = S.empty

composeTermSubst :: TermSubst -> TermSubst -> Infer TermSubst
composeTermSubst f g = (<>f) <$> traverse (substMeta f) g

{-
instance (Container a c,Substitutable b c) => Substitutable b a where
    subst s = runIdentity .
        (mapC :: (c -> Identity c) -> a -> Identity a) (Identity . subst s)
    free = execWriter .
        (mapC :: (c -> Writer (S.Set Name) c) -> a -> Writer (S.Set Name) a)
        (\c -> tell (free @b c) >> pure c)
-}