module Main where

import Test.Hspec

import Frontend
import qualified Foreign.Lua as L

main :: IO ()
main = hspec $ do
    pure ()