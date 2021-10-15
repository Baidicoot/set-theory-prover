module Kernel.ProofCheck where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except

import Kernel.Types
import Kernel.Eval
import qualified Kernel.TypeCheck as Ty

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

instThm :: Term -> Infer Term
instThm t = do
    m <- mapM (\n -> (,) n . MetaVar <$> free) (S.toList (free @Term t))
    pure (subst (M.fromList m) t)

infer :: ThmCtx -> ObjCtx -> Proof -> Infer Term
infer thms objs (Axiom n) = case M.lookup n ctx of
    Just t -> instThm t
    Nothing -> throwError (UnknownAxiom n)
infer thms objs (ModPon p0 p1) = do
    e0 <- infer thms objs p0
    e1 <- infer thms objs p1
    e' <- MetaVar <$> free
    s0 <- unifyTerms objs e0 (Imp e1 e')
    pure (subst s0 e')
infer thms objs (UniElim p0 e0) = do
    (_,t0) <- Ty.infer M.empty e0
    e1 <- infer thms objs p0
    e1' <- whnf e1
    case e1' of
        Forall x t1 e2 -> do
            s1 <- Ty.unifyPoly t0 t1
            pure (subst s1 e2)
        _ -> throwError (NotForall p0 e1')
infer thms objs Hole = do
    {- TBD -}