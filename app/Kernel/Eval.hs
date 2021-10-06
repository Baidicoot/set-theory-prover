{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
module Kernel.Eval where

import Kernel.Types
import Kernel.Subst

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Kernel.Subst (Substitutable)

{-
Kernel.Eval - equality checking between normal forms
-}

data DeBrujin
    = DLam DeBrujin
    | DApp DeBrujin DeBrujin
    | DVar Int
    | DAll DeBrujin
    | DImp DeBrujin DeBrujin
    | DConst Name
    | DHole Name
    deriving(Eq)

data EvalError
    = UnificationFail DeBrujin DeBrujin
    | HigherOrderUnification DeBrujin DeBrujin

type UniSubst = Subst DeBrujin
type Evaluator = Except EvalError 

instance Substitutable DeBrujin DeBrujin where
    subst s (DHole n) = case M.lookup n s of
        Just d -> d
        Nothing -> DHole n
    subst s (DLam d) = DLam (subst s d)
    subst s (DApp f x) = DApp (subst s f) (subst s x)
    subst s (DAll d) = DAll (subst s d)
    subst s (DImp a b) = DImp (subst s a) (subst s b)
    subst _ x = x

    free (DHole n) = S.singleton n
    free (DLam d) = free @DeBrujin d
    free (DApp f x) = S.union (free @DeBrujin f) (free @DeBrujin x)
    free (DAll d) = free @DeBrujin d
    free (DImp a b) = S.union (free @DeBrujin a) (free @DeBrujin b)
    free _ = S.empty

unify :: DeBrujin -> DeBrujin -> Evaluator UniSubst
unify x y | x == y = pure M.empty
unify (DLam a) (DLam b) = unify a b
unify (DAll a) (DAll b) = unify a b
unify (DImp a b) (DImp c d) = do
    f <- unify a c
    g <- unify b d
    pure (composeSubst f g)
unify a b = throwError (HigherOrderUnification a b)