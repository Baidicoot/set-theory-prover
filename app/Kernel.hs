module Kernel (module Kernel.ProofCheck, module Kernel.TypeCheck, module Kernel.Types, runProofCheck) where
{- namespacing, re-exports, etc -}

import Kernel.Types
import Kernel.ProofCheck
import Kernel.TypeCheck

runProofCheck :: [Name] -> Ctx -> Term -> Proof -> (Either ProofError (Term, [Term]), [Name])
runProofCheck ns ctx t p = (\(r, (ns,_)) -> case r of
    Left err -> (Left err, ns)
    Right (ts,hs,_) -> (Right (ts,hs), ns)) $ runInfer (ns,mempty) (checkThm ctx t p)