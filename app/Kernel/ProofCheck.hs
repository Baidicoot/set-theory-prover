{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
module Kernel.ProofCheck where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except

import Kernel.Types
import Kernel.Eval
import Kernel.Subst
import qualified Kernel.TypeCheck as Ty

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

instThm :: Term -> Infer Term
instThm t = do
    m <- mapM (\n -> (n,) . MetaVar <$> fresh) (S.toList (free @Term t))
    pure (subst (M.fromList m) t)

infer :: ThmCtx -> ObjCtx -> Proof -> Infer (Term, [Term])
infer thms objs (Axiom n) = case M.lookup n thms of
    Just t -> (,[]) <$> instThm t
    Nothing -> throwError (UnknownAxiom n)
infer thms objs (ModPon p0 p1) = do
    (e0,h0) <- infer thms objs p0
    (e1,h1) <- infer thms objs p1
    e' <- MetaVar <$> fresh
    (d2,s0) <- unifyTerms objs e0 (Imp e1 e')
    e2 <- subst s0 <$> substDBT d2 [] e'
    pure (e2,h0++h1)
infer thms objs (UniElim p0 e0) = do
    (_,t0) <- Ty.infer M.empty e0
    (e1,h) <- infer thms objs p0
    x' <- fresh
    t' <- TyVar <$> fresh
    e' <- MetaVar <$> fresh
    (d0,s0) <- unifyTerms objs e1 (Forall x' t' e')
    e2 <- subst s0 <$> substDBT d0 [] e'
    pure (e2,h)
infer thms objs Hole = (,[]) . MetaVar <$> fresh