module Kernel.ProofCheck where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Writer
import Control.Monad.Except

import Kernel.Types

{-
Check.hs - PROOF CHECKING
=========================
This actually checks the proofs
-}

type AxiomCtx = M.Map Name Term

infer :: AxiomCtx -> Proof -> Infer Term
infer ctx (Axiom n) = case M.lookup n ctx of
    Just t -> pure t
    Nothing -> throwError (UnknownAxiom n)
infer ctx (ModPon f x) = do
    ft <- infer ctx f
    xt <- infer ctx x
    