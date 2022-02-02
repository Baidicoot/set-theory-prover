module Kernel
    ( module Kernel.ProofCheck
    , module Kernel.TypeCheck
    , module Kernel.Types
    , runProofCheck
    , runPropCheck
    , runPropInfer
    , evalTerm
    , runGeneralize
    ) where
{- namespacing, re-exports, etc -}

import Kernel.Types
import Kernel.ProofCheck
import Kernel.TypeCheck
import Kernel.Subst
import qualified Kernel.Eval as E

runProofCheck :: [Name] -> Ctx -> Term -> Proof -> (Either (ProofError,[ProofTrace]) (Term, [Term]), [Name])
runProofCheck ns ctx t p = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (ts,hs,_) -> (Right (ts,hs), ns)) $ runInfer (ns,mempty) (checkThm ctx t p)

runPropCheck :: [Name] -> Ctx -> Monotype -> Term -> (Either (ProofError,[ProofTrace]) Term, [Name])
runPropCheck ns (_,ctx,_) s t = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (_,t) -> (Right t, ns)) $ runInfer (ns,mempty) (checkObj ctx t s)

runPropInfer :: [Name] -> Ctx -> Term -> (Either (ProofError,[ProofTrace]) (Term,Monotype), [Name])
runPropInfer ns (_,ctx,_) t = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (s,m) -> (Right (subst s t,m), ns)) $ runInfer (ns,mempty) (inferObj ctx t)

runGeneralize :: Monotype -> Polytype
runGeneralize = generalize mempty

evalTerm :: [Name] -> Ctx -> Term -> (Either (ProofError,[ProofTrace]) Term, [Name])
evalTerm ns (_,_,ctx) t = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right t -> (Right t, ns)) $ runInfer (ns,mempty) (E.whnfTerm ctx t)