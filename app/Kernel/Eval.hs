{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
module Kernel.Eval where

import Kernel.Types
import Kernel.Subst

import qualified Kernel.TypeCheck as Ty

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.IntMap as I
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import qualified Kernel.Subst as Ty

{-
Kernel.Eval - equality checking between type-erased normal forms
-}

instance Substitutable DeBrujin DeBrujin where
    subst s (DHole n) = case M.lookup n s of
        Just d -> d
        Nothing -> DHole n
    subst s (DLam d) = DLam (subst s d)
    subst s (DApp f x) = DApp (subst s f) (subst s x)
    subst s (DAll m d) = DAll m (subst s d)
    subst s (DImp a b) = DImp (subst s a) (subst s b)
    subst _ x = x

    free (DHole n) = S.singleton n
    free (DLam d) = free @DeBrujin d
    free (DApp f x) = S.union (free @DeBrujin f) (free @DeBrujin x)
    free (DAll _ d) = free @DeBrujin d
    free (DImp a b) = S.union (free @DeBrujin a) (free @DeBrujin b)
    free _ = S.empty

unifyD :: DeBrujin -> DeBrujin -> Infer (TermSubst, TypeSubst)
unifyD x y | x == y = pure (M.empty, M.empty)
unifyD (DLam a) (DLam b) = unifyD a b
unifyD (DAll t a) (DAll u b) = Ty.unify t u >> unifyD a b
unifyD (DImp a b) (DImp c d) = do
    (f,tf) <- unifyD a c
    (g,tg) <- unifyD b d
    pure (composeSubst f g, composeSubst tf tg)
unifyD a b = throwError (HigherOrderUnification a b)

shiftVars :: (Int -> Int) -> Int -> DeBrujin -> DeBrujin
shiftVars f i (DVar v) | v < i = DVar v
shiftVars f i (DVar v) | v >= i = DVar (v+1)
shiftVars f i (DLam b) = DLam (shiftVars f (f i) b)
shiftVars f i (DApp a b) = DApp (shiftVars f i a) (shiftVars f i b)
shiftVars f i (DAll m b) = DAll m (shiftVars f (f i) b)
shiftVars f i (DImp a b) = DImp (shiftVars f i a) (shiftVars f i b)
shiftVars _ _ x = x

substDeBrujin :: Int -> DeBrujin -> DeBrujin -> DeBrujin
substDeBrujin i st (DVar v) | i == v = st
substDeBrujin i st (DVar v) | i /= v = DVar v
substDeBrujin i st (DLam b) = DLam (substDeBrujin (i+1) (shiftVars (+1) 0 st) b)
substDeBrujin i st (DApp f a) = DApp (substDeBrujin i st f) (substDeBrujin i st a)
substDeBrujin i st (DAll m b) = DAll m (substDeBrujin (i+1) (shiftVars (+1) 0 st) b)
substDeBrujin i st (DImp f a) = DImp (substDeBrujin i st f) (substDeBrujin i st a)
substDeBrujin _ _ x = x

isConstApp :: DeBrujin -> Bool
isConstApp (DConst _) = True
isConstApp (DApp f _) = isConstApp f
isConstApp _ = False

whnfDeBrujin :: DeBrujin -> Infer DeBrujin
whnfDeBrujin (DLam a) = pure (DLam a)
whnfDeBrujin (DApp f x) = do
    f' <- whnfDeBrujin f
    case f' of
      DLam b -> whnfDeBrujin (substDeBrujin 0 x b)
      x | isConstApp x -> fmap (DApp x) (whnfDeBrujin x)
      x -> throwError (NonFunctionEval x)
whnfDeBrujin (DAll m a) = fmap (DAll m) (whnfDeBrujin a)
whnfDeBrujin (DImp a b) = liftM2 DImp (whnfDeBrujin a) (whnfDeBrujin b)
whnfDeBrujin (DHole x) = pure (DHole x)
whnfDeBrujin x = throwError (NoEvalRule x)

termToDeBrujin :: M.Map Name Int -> Term -> DeBrujin
termToDeBrujin m (Var n) = case M.lookup n m of
    Just i -> DVar i
    Nothing -> DConst n
termToDeBrujin m (Lam n b) = DLam (termToDeBrujin (M.insert n 0 (fmap (+1) m)) b)
termToDeBrujin m (Forall n t b) = DAll t (termToDeBrujin (M.insert n 0 (fmap (+1) m)) b)
termToDeBrujin m (Let n x t) =
    DApp (DLam (termToDeBrujin (M.insert n 0 (fmap (+1) m)) t)) (termToDeBrujin m x)
termToDeBrujin m (App f x) =
    DApp (termToDeBrujin m f) (termToDeBrujin m x)
termToDeBrujin m (Imp a b) =
    DImp (termToDeBrujin m a) (termToDeBrujin m b)

deBrujinToTerm :: [Name] -> DeBrujin -> Infer Term
deBrujinToTerm ns (DLam a) = do
    x <- fresh
    a' <- deBrujinToTerm (x:ns) a
    pure (Lam x a')
deBrujinToTerm ns (DVar n) = pure (ns !! n)
deBrujinToTerm ns (DApp e0 e1) = do
    e0' <- deBrujinToTerm ns e0
    e1' <- deBrujinToTerm ns e1
    pure (App e0' e1')
deBrujinToTerm ns (DImp e0 e1) = do
    e0' <- deBrujinToTerm ns e0
    e1' <- deBrujinToTerm ns e1
    pure (Imp e0' e1')