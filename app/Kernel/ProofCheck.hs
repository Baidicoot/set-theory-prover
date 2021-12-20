{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module Kernel.ProofCheck (checkThm, inferThm) where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except

import Data.Maybe (fromMaybe)

import Kernel.Types
import Kernel.Eval
import Kernel.Subst
import Kernel.TypeCheck

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

type FullSubst = (TermSubst, TypeSubst)

substFull :: (Container t Term,Substitutable Monotype t) => FullSubst -> t -> Infer t
substFull (d,s) t = mapC (substRenaming substMetaVarsTerm d) (subst s t)

{- left-biased composition -}
composeFull :: FullSubst -> FullSubst -> Infer FullSubst
composeFull (d0,s0) (d1,s1) = (,composeSubst s0 s1) <$>
    composeRenamingSubst substMetaVarsTerm (subst s1 d0) (subst s0 d1)

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b

trd3 :: (a,b,c) -> c
trd3 (_,_,c) = c

addThm :: Name -> Term -> Ctx -> Ctx
addThm n t (a,b,c) = (M.insert n t a,b,c)

addObj :: Name -> Polytype -> Ctx -> Ctx
addObj n t (a,b,c) = (a,M.insert n t b,c)

updateCtx :: FullSubst -> Ctx -> Infer Ctx
updateCtx f (a,b,c) = do
    a' <- substFull f a
    let b' = subst (snd f) b
    c' <- substFull f c
    pure (a',b',c')

{- replaces all MetaVars with fresh ones -}
instThm :: Term -> Infer Term
instThm t = do
    m <- mapM (\n -> (n,) . MetaVar <$> fresh) (S.toList (free @Term t))
    pure (subst (M.fromList m) t)

-- add things for checking props inside this
checkThm :: Ctx -> Term -> Proof -> Infer (Term, [Term], FullSubst)
checkThm ctx t p = traceErr ("checking " ++ show p ++ " proves " ++ show t) (checkThm' ctx t p)
    where
    checkThm' ctx e0 (IntroThm n t p) = do
        (s0,_) <- inferObj (snd3 ctx) t
        e1 <- MetaVar <$> fresh
        e2 <- MetaVar <$> fresh
        f0 <- unifyTerm (trd3 ctx) (subst s0 e0) (Imp e1 e2)
        ctx <- updateCtx f0 ctx
        e1' <- substFull f0 e1
        e2' <- substFull f0 e2
        (_,h,f1) <- checkThm (addThm n e1' ctx) e2' p
        ctx <- updateCtx f1 ctx
        e1'' <- substFull f1 e1'
        e2'' <- substFull f1 e2'
        f2 <- unifyTerm (trd3 ctx) e1'' t
        e1''' <- substFull f2 e1''
        e2''' <- substFull f2 e2''
        h' <- mapM (substFull f2) h
        f <- composeFull f2 =<< composeFull f1 f0
        pure (Imp e1''' e2''',h',f)
    checkThm' ctx e0 (IntroObj n t p) = do
        t0 <- TyVar <$> fresh
        e1 <- MetaVar <$> fresh
        x' <- fresh
        f0 <- unifyTerm (trd3 ctx) e0 (Forall x' t0 e1)
        ctx <- updateCtx f0 ctx
        e1' <- substFull f0 e1
        let t0' = subst (snd f0) t0
        (_,h,f1) <- checkThm (addObj n (Polytype S.empty t0') ctx) e1' p
        e1'' <- substFull f1 e1'
        ctx <- updateCtx f1 ctx
        let t0'' = subst (snd f1) t0'
        f2 <- (mempty,) <$> unifyTyp t0'' t
        let t0''' = subst (snd f2) t0''
        h' <- mapM (substFull f2) h
        e1''' <- substFull f2 e1''
        f <- composeFull f2 =<< composeFull f1 f0
        pure (Forall x' t0''' e1'',h',f)
    checkThm' ctx e0 p = do
        (e1,h,f0) <- inferThm ctx p
        e0' <- substFull f0 e0
        f1 <- unifyTerm (trd3 ctx) e0' e1
        e1' <- substFull f1 e1
        f <- composeFull f1 f0
        (e1',,f) <$> mapM (substFull f1) h

inferThm :: Ctx -> Proof -> Infer (Term, [Term], FullSubst)
inferThm ctx p = traceErr ("checking proof " ++ show p) (inferThm' ctx p)
    where
    inferThm' ctx (Axiom n) = case M.lookup n (fst3 ctx) of
        Just t -> (,[],mempty) <$> instThm t
        Nothing -> throwErr (UnknownAxiom n)
    inferThm' ctx (Param n) = case M.lookup n (fst3 ctx) of
        Just t -> (,[],mempty) <$> instThm t
        Nothing -> throwErr (UnknownAxiom n)
    inferThm' ctx (ModPon p0 p1) = do
        (e0,h0,f0) <- inferThm ctx p0
        p1' <- substFull f0 p1
        ctx <- updateCtx f0 ctx
        (e1,h1,f1) <- inferThm ctx p1'
        h0' <- mapM (substFull f1) h0
        ctx <- updateCtx f1 ctx
        e' <- MetaVar <$> fresh
        e0' <- substFull f1 e0
        f2 <- unifyTerm (trd3 ctx) e0' (Imp e1 e')
        e2 <- substFull f2 e'
        h0'' <- mapM (substFull f2) h0'
        h1' <- mapM (substFull f2) h1
        f <- composeFull f2 =<< composeFull f1 f0
        pure (e2,h0''++h1',f)
    inferThm' ctx (IntroThm n e0 p) = do
        (s0,_) <- inferObj (snd3 ctx) e0
        (e1,h,f1) <- inferThm (addThm n e0 ctx) p
        e0' <- substFull f1 e0
        pure (Imp e0' e1,fmap (subst s0) h,f1)
    inferThm' ctx (UniElim p0 e0) = do
        (s0,t0) <- inferObj (snd3 ctx) e0
        (e1,h,f1) <- inferThm ctx p0
        ctx <- updateCtx f1 ctx
        e1' <- whnfTerm (trd3 ctx) e1
        case e1' of
            Forall x t e -> do
                _ <- unifyTyp t t0
                e0' <- substFull f1 e0
                pure (App (Lam x e) e0',h,f1)
            _ -> throwErr (NotForall p0 e0)
    {- maybe replace this with something that attempts to? -}
    inferThm' ctx (IntroObj n t p) = throwErr (CantInferHigherOrder n p)
    inferThm' ctx Hole = (\t -> (t,[t],(M.empty,M.empty))) . MetaVar <$> fresh