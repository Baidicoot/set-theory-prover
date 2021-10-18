{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
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

{- replaces all MetaVars with fresh ones -}
instThm :: Term -> Infer Term
instThm t = do
    m <- mapM (\n -> (n,) . MetaVar <$> fresh) (S.toList (free @Term t))
    pure (subst (M.fromList m) t)

checkThm :: ThmCtx -> ObjCtx -> Term -> Proof -> Infer [Term]
checkThm thms objs e0 p = do
    (e1,h) <- inferThm thms objs p
    (s0,s1) <- unifyObj objs e0 e1
    mapM (substObj s0 [] . subst s1) h

inferThm :: ThmCtx -> ObjCtx -> Proof -> Infer (Term, [Term])
inferThm thms objs (Axiom n) = case M.lookup n thms of
    Just t -> (,[]) <$> instThm t
    Nothing -> throwError (UnknownAxiom n)
inferThm thms objs (ModPon p0 p1) = do
    (e0,h0) <- inferThm thms objs p0
    (e1,h1) <- inferThm thms objs p1
    e' <- MetaVar <$> fresh
    (d2,s0) <- unifyObj objs e0 (Imp e1 e')
    e2 <- subst s0 <$> substObj d2 [] e'
    pure (e2,h0++h1)
inferThm thms objs (UniElim p0 e0) = do
    (_,t0) <- inferObj M.empty e0
    (e1,h) <- inferThm thms objs p0
    x' <- fresh
    t' <- TyVar <$> fresh
    e' <- MetaVar <$> fresh
    (d0,s0) <- unifyObj objs e1 (Forall x' t' e')
    e2 <- subst s0 <$> substObj d0 [] e'
    pure (e2,h)
inferThm thms objs Hole = (,[]) . MetaVar <$> fresh