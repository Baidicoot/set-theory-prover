{-# LANGUAGE MultiParamTypeClasses #-}
module Kernel.Subst where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad
import Control.Monad.State
import Control.Monad.Except

type Subst = M.Map Name

composeSubst :: (Subst a -> a -> a) Subst a -> Subst a -> Subst a
composeSubst subst f g = fmap (subst f) g `M.union` f

class Substitutable a b where
    subst :: Subst a -> a -> a
    free :: a -> S.Set Name