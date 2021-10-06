{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Kernel.Subst where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

import Kernel.Types

type Subst = M.Map Name

composeSubst :: Substitutable a a => Subst a -> Subst a -> Subst a
composeSubst f g = fmap (subst f) g `M.union` f

class Substitutable a b where
    subst :: Subst a -> b -> b
    free :: b -> S.Set Name