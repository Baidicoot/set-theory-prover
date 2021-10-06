module Check where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except

import Kernel.Logic

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

data ProofOutput
    = FoundHole Term

data ProofError
    = DoesNotMatch Proof Term

type Checker = ExceptT Writer [ProofOutput]

unify :: Term -> Term -> Checker Subst

infer :: Proof -> Checker Term
infer (ModPon a b) = do
    t <- check 