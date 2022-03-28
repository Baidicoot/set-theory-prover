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
import Control.Monad.Trace

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
substFull (d,s) t = mapC (substMeta d) (subst s t)

{- left-biased composition -}
composeFull :: FullSubst -> FullSubst -> Infer FullSubst
composeFull (d0,s0) (d1,s1) = (,composeSubst s0 s1) <$>
    composeTermSubst (subst s1 d0) (subst s0 d1)

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
    substMeta (M.fromList m) t

-- demystify using good variable names
checkThm :: Ctx -> Term -> Proof -> Infer (Term, [Term], FullSubst)
checkThm context theorem proof = traceError (CheckingProof proof theorem)
    (checkThm' context theorem proof)
    where
    checkThm' ctx thm (IntroThm varName varType prf) = do
        (s0,_) <- inferObj (snd3 ctx) varType
        lhs <- MetaVar <$> fresh
        rhs <- MetaVar <$> fresh
        f0 <- unifyTerm (trd3 ctx) (subst s0 thm) (Imp lhs rhs)
        ctx <- updateCtx f0 ctx
        lhs <- substFull f0 lhs
        rhs <- substFull f0 rhs
        (_,holes,f1) <- checkThm (addThm varName lhs ctx) rhs prf
        ctx <- updateCtx f1 ctx
        lhs <- substFull f1 lhs
        rhs <- substFull f1 rhs
        f2 <- unifyTerm (trd3 ctx) lhs varType
        lhs <- substFull f2 lhs
        rhs <- substFull f2 rhs
        holes <- mapM (substFull f2) holes
        f <- composeFull f2 =<< composeFull f1 f0
        pure (Imp lhs rhs,holes,f)
    checkThm' ctx thm (IntroObj varName varType prf) = do
        thm <- whnfTerm (trd3 ctx) thm
        case thm of
            Forall varNameThm varTypeThm restOfThm -> do
                s0 <- unifyTyp varType varTypeThm
                let restOfThm' = subst (M.singleton varNameThm (Var varName)) restOfThm
                (thm,holes,f0) <- checkThm (addObj varName (Polytype S.empty $ subst s0 varType) ctx) restOfThm' prf
                f <- composeFull (mempty,s0) f0
                pure (thm,holes,f)
            _ -> throwError (NotForall (IntroObj varName varType prf) thm)
    checkThm' ctx thm prf = do
        (thm',holes,f0) <- inferThm ctx prf
        thm <- substFull f0 thm
        f1 <- unifyTerm (trd3 ctx) thm thm'
        thm <- substFull f1 thm
        f <- composeFull f1 f0
        (thm,,f) <$> mapM (substFull f1) holes

inferThm :: Ctx -> Proof -> Infer (Term, [Term], FullSubst)
inferThm context proof = traceError (InferringProof proof) (inferThm' context proof)
    where
    inferThm' ctx (Axiom axName) = case M.lookup axName (fst3 ctx) of
        Just thm -> (,[],mempty) <$> instThm thm
        Nothing -> throwError (UnknownAxiom axName)
    inferThm' ctx (ModPon func arg) = do
        (funcTy,holes,f0) <- inferThm ctx func
        arg <- substFull f0 arg
        ctx <- updateCtx f0 ctx
        (argTy,holes',f1) <- inferThm ctx arg
        func <- substFull f1 func
        holes <- (++holes') <$> mapM (substFull f1) holes
        ctx <- updateCtx f1 ctx
        rhs <- MetaVar <$> fresh
        f2 <- unifyTerm (trd3 ctx) funcTy (Imp argTy rhs)
        rhs <- substFull f2 rhs
        holes <- mapM (substFull f2) holes
        f <- composeFull f2 =<< composeFull f1 f0
        pure (rhs,holes,f)
    inferThm' ctx (IntroThm varName varType prf) = do
        (s0,_) <- inferObj (snd3 ctx) varType
        (rhs,holes,f1) <- inferThm (addThm varName varType ctx) prf
        varType <- substFull f1 varType
        pure (Imp varType rhs,fmap (subst s0) holes,f1)
    inferThm' ctx (UniElim prf obj) = do
        (s0,objType) <- inferObj (snd3 ctx) obj
        (func,holes,f0) <- inferThm ctx (subst s0 prf)
        ctx <- updateCtx f0 ctx
        obj <- substFull f0 obj
        func <- whnfTerm (trd3 ctx) func
        case func of
            Forall x t e -> do
                s1 <- unifyTyp t objType
                pure (App (Lam x e) obj,subst s0 (subst s1 holes),f0)
            _ -> throwError (NotForall prf obj)
    {- maybe replace this with something that attempts to? -}
    inferThm' ctx (IntroObj varName varType prf) = throwError (CantInferHigherOrder varName prf)
    inferThm' ctx Hole = (\t -> (t,[t],(M.empty,M.empty))) . MetaVar <$> fresh