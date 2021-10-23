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

import Kernel.Types
import Kernel.Eval
import Kernel.Subst
import Kernel.TypeCheck

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

type FullSubst = (DeBrujinSubst, TypeSubst)

substFull :: (SubstDeBrujin t,Substitutable Monotype t) => FullSubst -> t -> Infer t
substFull (d,s) t = substObj d (subst s t)

{- left-biased composition -}
composeFull :: FullSubst -> FullSubst -> FullSubst
composeFull (d0,s0) (d1,s1) = (composeSubst (subst s1 d0) (subst s0 d1),composeSubst s0 s1)

{- replaces all MetaVars with fresh ones -}
instThm :: Term -> Infer Term
instThm t = do
    m <- mapM (\n -> (n,) . MetaVar <$> fresh) (S.toList (free @Term t))
    pure (subst (M.fromList m) t)

checkThm :: ThmCtx -> ObjCtx -> Term -> Proof -> Infer [Term]
checkThm thms objs e0 p = do
    (e1,h,f0) <- inferThm thms objs p
    e0' <- substFull f0 e0
    f1 <- unifyObj objs e0' e1
    mapM (substFull f1) h

inferThm :: ThmCtx -> ObjCtx -> Proof -> Infer (Term, [Term], FullSubst)
inferThm thms objs (Axiom n) = case M.lookup n thms of
    Just t -> (,[],(M.empty,M.empty)) <$> instThm t
    Nothing -> throwError (UnknownAxiom n)
inferThm thms objs (ModPon p0 p1) = do
    (e0,h0,f0) <- inferThm thms objs p0
    p1' <- substFull f0 p1
    (e1,h1,f1) <- inferThm thms objs p1'
    e' <- MetaVar <$> fresh
    e0' <- substFull f1 e0
    f2 <- unifyObj objs e0' (Imp e1 e')
    e2 <- substFull f2 e'
    pure (e2,h0++h1,composeFull f2 (composeFull f1 f0))
inferThm thms objs (IntrosThm n p) = do
    e0 <- MetaVar <$> fresh
    (e1,h,f1) <- inferThm (M.insert n e0 thms) objs p
    e0' <- substFull f1 e0
    pure (Imp e0' e1,h,f1)
inferThm thms objs (UniElim p0 e0) = do
    (s0,t0) <- inferObj M.empty e0
    (e1,h,f1) <- inferThm thms objs p0
    x' <- fresh
    t' <- TyVar <$> fresh
    e' <- MetaVar <$> fresh
    f2 <- unifyObj objs e1 (Forall x' t' e')
    e2 <- substFull f2 e'
    pure (e2,h,composeFull f2 f1)
{- need to switch to a bimodal (check vs infer) typechecker algo -}
inferThm thms objs (IntrosObj n p) = _
inferThm thms objs Hole = (,[],(M.empty,M.empty)) . MetaVar <$> fresh