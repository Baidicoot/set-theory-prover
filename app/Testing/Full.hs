module Main where

import qualified Data.ByteString as B

import RunLua
import Test.Hspec
import Data.ByteString.Char8 (unpack)

runProofFile :: String -> IO (Either String String)
runProofFile s = do
    prg <- B.readFile s
    fst <$> runProofScript prg

succeeds :: String -> String -> Spec
succeeds n f = do
    o <- runIO (runProofFile f)
    --runIO (print o)
    it n $ case o of
        Right _ -> True
        Left _ -> False

fails :: String -> String -> Spec
fails n f = do
    o <- runIO (runProofFile f)
    --runIO (print o)
    it n $ case o of
        Right _ -> False
        Left _ -> True

main :: IO ()
main = hspec $ do
    describe "notations" $
        succeeds "infix"
            "app/Testing/FullTests/notation.lua"
    describe "logic" $ do
        succeeds "logic_succeeds"
            "app/Testing/FullTests/logic_s.lua"
        fails "logic_fails"
            "app/Testing/FullTests/logic_f.lua"
    describe "interface" $
        succeeds "interface"
            "app/Testing/FullTests/interface.lua"
    describe "serialize" $ do
        succeeds "serialize"
            "app/Testing/FullTests/serialize.lua"
        succeeds "deserialize"
            "app/Testing/FullTests/deserialize.lua"