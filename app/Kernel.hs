module Kernel (module Kernel.ProofCheck, module Kernel.TypeCheck, module Kernel.Types) where
{- namespacing, re-exports, etc -}

import Kernel.Types hiding(Name)
import Kernel.ProofCheck
import Kernel.TypeCheck

runProofCheck :: [Name] -> Ctx -> Term -> Proof -> (Either ProofError (Term, [Term]), [Name])
runProofCheck ns ctx t p = do