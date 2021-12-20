{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Kernel.Eval (simpObj, unifyObj, evalObj, SubstDeBrujin(..)) where

import Kernel.Types
import Kernel.Subst

import Kernel.TypeCheck

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.IntMap as I
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except

import Data.Maybe (fromMaybe)

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

{- free variables vs bound variables are already handled -}
instance Substitutable Term Term where
    subst s (MetaVar n) = case M.lookup n s of
        Just e -> e
        Nothing -> MetaVar n
    subst s (Lam n e) = Lam n (subst s e)
    subst s (Let n e0 e1) = Let n (subst s e0) (subst s e1)
    subst s (App e0 e1) = App (subst s e0) (subst s e1)
    subst s (Imp e0 e1) = Imp (subst s e0) (subst s e1)
    subst s (Forall n t e) = Forall n t (subst s e)
    subst _ x = x

    free (MetaVar n) = S.singleton n
    free (Lam _ e) = free @Term e
    free (Let _ e0 e1) = free @Term e0 `S.union` free @Term e1
    free (App e0 e1) = free @Term e0 `S.union` free @Term e1
    free (Imp e0 e1) = free @Term e0 `S.union` free @Term e1
    free (Forall _ _ e) = free @Term e
    free _ = S.empty

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

{-
reduceWhnfDeBrujin requires at least one reduction
whnfDeBrujin does not require any reduction
-}

reduceWhnfDeBrujin :: DefCtx -> DeBrujin -> Maybe DeBrujin
reduceWhnfDeBrujin ctx (DApp f x) =
    case whnfDeBrujin ctx f of
      DLam d -> Just $ whnfDeBrujin ctx (substDeBrujin 0 x d)
      _ -> Nothing
reduceWhnfDeBrujin ctx (DConst n) = M.lookup n ctx
reduceWhnfDeBrujin _ _ = Nothing

whnfDeBrujin :: DefCtx -> DeBrujin -> DeBrujin
whnfDeBrujin ctx (DApp f x) = case whnfDeBrujin ctx f of
    DLam d -> whnfDeBrujin ctx (substDeBrujin 0 x d)
    x -> x
whnfDeBrujin ctx (DConst n) = fromMaybe (DConst n) (M.lookup n ctx)
whnfDeBrujin _ x = x

occurs :: Substitutable DeBrujin b => Name -> b -> Bool
occurs n = S.member n . free @DeBrujin

unifyD :: DefCtx -> DeBrujin -> DeBrujin -> Infer (DeBrujinSubst, TypeSubst)
unifyD ctx x y = traceErr ("unifying " ++ show x ++ " and " ++ show y) (unifyD' ctx x y)
    where
    unifyD' ctx x y | x == y = pure mempty
    unifyD' ctx (DHole x) y | not (occurs x y) = pure (M.singleton x y,mempty)
    unifyD' ctx y (DHole x) | not (occurs x y) = pure (M.singleton x y,mempty)
    unifyD' ctx (DLam a) (DLam b) = unifyD ctx a b
    unifyD' ctx (DAll t a) (DAll u b) = unifyTyp t u >> unifyD ctx a b
    unifyD' ctx (DImp a b) (DImp c d) = do
        (f,tf) <- unifyD ctx a c
        (g,tg) <- unifyD ctx b d
        pure (f<+g, tf<+tg)
    unifyD' ctx a b =
        case (reduceWhnfDeBrujin ctx a,reduceWhnfDeBrujin ctx b) of
            (Nothing,Nothing) -> throwErr (ObjectUnificationFail a b)
            (Just a,Nothing) -> unifyD ctx a b
            (Nothing,Just b) -> unifyD ctx a b
            (Just a, Just b) -> unifyD ctx a b

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
termToDeBrujin m (Const n) = DConst n
termToDeBrujin m (MetaVar n) = DHole n

deBrujinToTerm :: [Name] -> DeBrujin -> Infer Term
deBrujinToTerm ns d = traceErr (show "reforming " ++ show d ++ " in context" ++ show ns) (deBrujinToTerm' ns d)
    where
    deBrujinToTerm' ns (DLam a) = do
        x <- fresh
        a' <- deBrujinToTerm (x:ns) a
        pure (Lam x a')
    deBrujinToTerm' ns (DAll t a) = do
        x <- fresh
        a' <- deBrujinToTerm (x:ns) a
        pure (Forall x t a')
    deBrujinToTerm' ns (DVar n) | length ns > n = pure (Var $ ns !! n)
    deBrujinToTerm' ns (DVar n) = throwErr (UnscopedDeBrujin n)
    deBrujinToTerm' ns (DApp e0 e1) = do
        e0' <- deBrujinToTerm ns e0
        e1' <- deBrujinToTerm ns e1
        pure (App e0' e1')
    deBrujinToTerm' ns (DImp e0 e1) = do
        e0' <- deBrujinToTerm ns e0
        e1' <- deBrujinToTerm ns e1
        pure (Imp e0' e1')
    deBrujinToTerm' _ (DConst n) = pure (Const n)
    deBrujinToTerm' _ (DHole n) = pure (MetaVar n)
    deBrujinToTerm' _ (DFree n) = pure (Var n)

{- factor into typeclass -}
class SubstDeBrujin t where
    substObj :: DeBrujinSubst -> t -> Infer t

instance (Traversable t,SubstDeBrujin a) => SubstDeBrujin (t a) where
    substObj = traverse . substObj

{- dummy instance -}
instance SubstDeBrujin Polytype where
    substObj _ t = pure t

instance SubstDeBrujin Term where
    -- unifyD can bind deBrujin terms with local variables, fix
    substObj s (MetaVar n) = case M.lookup n s of
            Just e -> deBrujinToTerm [] e
            Nothing -> pure (MetaVar n)
    substObj s (Lam n e) = Lam n <$> substObj s e
    substObj s (Let n e0 e1) = liftM2 (Let n) (substObj s e0) (substObj s e1)
    substObj s (App e0 e1) =  liftM2 App (substObj s e0) (substObj s e1)
    substObj s (Imp e0 e1) = liftM2 Imp (substObj s e0) (substObj s e1)
    substObj s (Forall n t e) = Forall n t <$> substObj s e
    substObj _ x = pure x

instance SubstDeBrujin DeBrujin where
    substObj s = pure . subst s

{-
this requires UndecidableInstances:
instance Container a Term => SubstDeBrujin a where
so it needs to be done manually:
-}

instance SubstDeBrujin Proof where
    substObj = mapC . (substObj :: DeBrujinSubst -> Term -> Infer Term)

evalObj :: DefCtx -> Term -> DeBrujin
evalObj ctx t = let d = termToDeBrujin M.empty t in whnfDeBrujin ctx d

simpObj :: DefCtx -> Term -> Infer Term
simpObj ctx t =
    let d = termToDeBrujin M.empty t in
    deBrujinToTerm [] (whnfDeBrujin ctx d)

unifyObj :: DefCtx -> Term -> Term -> Infer (DeBrujinSubst, TypeSubst)
unifyObj ctx t0 t1 = do
    let d0 = termToDeBrujin M.empty t0
    let d1 = termToDeBrujin M.empty t1
    (sd,st) <- unifyD ctx d0 d1
    pure (sd, st)