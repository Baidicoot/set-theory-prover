{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Kernel.Subst where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Kernel.Types

type Subst = M.Map Name

type DeBrujinSubst = Subst DeBrujin
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

instance Substitutable a b => Substitutable a (M.Map c b) where
    subst s m = fmap (subst s) m
    free m = S.unions (M.elems $ fmap (free @a) m)