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

type DeBrujinSubst = Subst DeBrujin
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

instance Container Proof Term where
    mapC f (ModPon a b) = liftM2 ModPon (mapC f a) (mapC f b)
    mapC f (UniElim p t) = liftM2 UniElim (mapC f p) (f t)
    mapC f (IntrosObj n t p) = fmap (IntrosObj n t) (mapC f p)
    mapC f (IntrosThm n t p) = liftM2 (IntrosThm n) (f t) (mapC f p)
    mapC _ x = pure x

instance Container Term Monotype where
    mapC f (Lam n e) = fmap (Lam n) (mapC f e)
    mapC f (Let n e0 e1) = liftM2 (Let n) (mapC f e0) (mapC f e1)
    mapC f (App e0 e1) = liftM2 App (mapC f e0) (mapC f e1)
    mapC f (Imp e0 e1) = liftM2 App (mapC f e0) (mapC f e1)
    mapC f (Forall n t e) = liftM2 (Forall n) (f t) (mapC f e)
    mapC _ x = pure x

instance Container DeBrujin Monotype where
    mapC f (DLam d) = mapC f d
    mapC f (DApp d0 d1) = liftM2 DApp (mapC f d0) (mapC f d1)
    mapC f (DImp d0 d1) = liftM2 DImp (mapC f d0) (mapC f d1)
    mapC f (DAll t d) = liftM2 DAll (f t) (mapC f d)
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

instance Substitutable Monotype DeBrujin where
    subst s = runIdentity .
        (mapC :: (Monotype -> Identity Monotype) -> DeBrujin -> Identity DeBrujin) (Identity . subst s)
    free = execWriter .
        (mapC :: (Monotype -> Writer (S.Set Name) Monotype) -> DeBrujin -> Writer (S.Set Name) DeBrujin)
        (\c -> tell (free @Monotype c) >> pure c)

{-
instance (Container a c,Substitutable b c) => Substitutable b a where
    subst s = runIdentity .
        (mapC :: (c -> Identity c) -> a -> Identity a) (Identity . subst s)
    free = execWriter .
        (mapC :: (c -> Writer (S.Set Name) c) -> a -> Writer (S.Set Name) a)
        (\c -> tell (free @b c) >> pure c)
-}