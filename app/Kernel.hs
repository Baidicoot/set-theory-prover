module Kernel
    ( module Kernel.ProofCheck
    , module Kernel.TypeCheck
    , module Kernel.Types
    , runProofCheck
    , runPropCheck
    , runPropInfer
    , evalObj
    ) where
{- namespacing, re-exports, etc -}

import Kernel.Types
import Kernel.ProofCheck
import Kernel.TypeCheck
import Kernel.Subst
import qualified Kernel.Eval as E

runProofCheck :: [Name] -> Ctx -> Term -> Proof -> (Either ProofError (Term, [Term]), [Name])
runProofCheck ns ctx t p = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (ts,hs,_) -> (Right (ts,hs), ns)) $ runInfer (ns,mempty) (checkThm ctx t p)

runPropCheck :: [Name] -> Ctx -> Monotype -> Term -> (Either ProofError Term, [Name])
runPropCheck ns (_,ctx,_) s t = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (_,t) -> (Right t, ns)) $ runInfer (ns,mempty) (checkObj ctx t s)

runPropInfer :: [Name] -> Ctx -> Term -> (Either ProofError (Term,Monotype), [Name])
runPropInfer ns (_,ctx,_) t = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (s,m) -> (Right (subst s t,m), ns)) $ runInfer (ns,mempty) (inferObj ctx t)

evalObj :: Ctx -> Term -> DeBrujin
evalObj (_,_,ctx) = E.evalObj ctx