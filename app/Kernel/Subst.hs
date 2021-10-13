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

type TermSubst = Subst DeBrujin
type TypeSubst = Subst Monotype

{- LEFT-BIASED COMPOSITION -}
composeSubst :: Substitutable a a => Subst a -> Subst a -> Subst a
composeSubst f g = fmap (subst f) g `M.union` f

(<:) = composeSubst

infixr 0 <:

class Substitutable a b where
    subst :: Subst a -> b -> b
    free :: b -> S.Set Name

instance Substitutable a b => Substitutable a (Maybe b) where
    subst s (Just b) = Just (subst s b)
    subst _ Nothing = Nothing

    free (Just b) = free @a b
    free Nothing = S.empty