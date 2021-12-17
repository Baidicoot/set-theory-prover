{-# LANGUAGE ScopedTypeVariables #-}
module Main where
import Frontend
import qualified Foreign.Lua as L
import Data.IORef
import System.IO
import System.Environment
import qualified Data.Text as T
import ParserTypes
import Control.Exception
import Control.Monad

import qualified Data.ByteString as B

import Data.Char(ord)

initialNames :: [Name]
initialNames = fmap (T.pack . ("v"++) . show) [1..]

catchScriptError :: L.Lua L.Status -> L.Lua ()
catchScriptError f = do
    s <- f
    case s of
        L.OK -> pure ()
        L.Yield -> L.liftIO (putStrLn "YIELDING FROM SCRIPT FILE UNSUPPORTED")
        _ -> do
            err <- L.peek 1
            L.liftIO (putStrLn ("script errored with: " ++ err))

runFile :: IORef (ProverState,([Name],Maybe Grammar)) -> String -> IO ()
runFile state filepath = L.run $ do
    L.openlibs
    L.registerHaskellFunction "refine" (runExt "refine" refineExt state)
    L.registerHaskellFunction "assert" (curry $ runExt "assert" assertExt state)
    L.registerHaskellFunction "sort" (runExt "sort" newSortExt state)
    L.registerHaskellFunction "beginProof" (runExt "beginProof" beginProofExt state)
    L.registerHaskellFunction "endProof" (runExt "endProof" endProofExt state)
    L.registerHaskellFunction "const" (curry $ runExt "const" newConstExt state)
    L.registerHaskellFunction "notation" (curry $ runExt "notation" notationExt state)
    L.registerHaskellFunction "die" (runActionExt "die" dieExt state)
    L.registerHaskellFunction "printGrammar" (runActionExt "printGrammar" printGrammarExt state)
    L.registerHaskellFunction "done" (runActionExt "done" doneExt state)
    L.registerHaskellFunction "loadState" (runExt "loadState" loadStateExt state)
    L.registerHaskellFunction "includeState" (runExt "includeState" loadStateExt state)
    L.registerHaskellFunction "dumpState" (runOutputExt "dumpState" dumpStateExt state)
    L.registerHaskellFunction "define" (curry $ runExt "define" defineExt state)
    catchScriptError $ L.dofile filepath

main :: IO ()
main = do
    putStrLn "Welcome to SPARSE RECAPITALIZATION™."
    putStrLn "© Aidan Ewart, 2021"
    args <- getArgs
    state <- newIORef (initialState,(initialNames,Nothing))
    runFile state (head args)
    ((_,env,_),_) <- readIORef state
    putStrLn "exited with environment:"
    print env
    pure ()