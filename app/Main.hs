{-# LANGUAGE ScopedTypeVariables #-}
module Main where
import Frontend
import qualified Foreign.Lua as L
import Data.IORef
import System.IO
import qualified Data.Text as T
import ParserTypes
import Control.Exception
import Control.Monad

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

main :: IO ()
main = do
    putStrLn "Welcome to SPARSE RECAPITALIZATION™."
    putStrLn "© Aidan Ewart, 2021"
    putStr "> runfile "
    hFlush stdout
    filepath <- getLine
    state <- newIORef (initialState,initialNames)
    L.run $ do
        L.openlibs
        L.registerHaskellFunction "refine" (runExt "refine" refineExt state)
        L.registerHaskellFunction "assert" (curry $ runExt "assert" assertExt state)
        L.registerHaskellFunction "sort" (runExt "sort" newSortExt state)
        L.registerHaskellFunction "beginProof" (runExt "beginProof" beginProofExt state)
        L.registerHaskellFunction "endProof" (runExt "endProof" endProofExt state)
        L.registerHaskellFunction "const" (curry $ runExt "const" newConstExt state)
        L.registerHaskellFunction "die" (\x -> L.liftIO (putStrLn x) >> L.raiseError x)
        catchScriptError $ L.dofile filepath
    ((_,env,_),_) <- readIORef state
    putStrLn "exited with environment:"
    print env
    pure ()