module Main where

import Test.Hspec

import Kernel
import Kernel.Eval
import Kernel.ProofCheck
import Kernel.Subst
import Kernel.TypeCheck
import Kernel.Types

main :: IO ()
main = hspec $ do
    pure ()