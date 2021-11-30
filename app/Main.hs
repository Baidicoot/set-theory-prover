module Main where
import Frontend
import qualified Foreign.Lua as L
import Data.IORef
import System.IO

main :: IO ()
main = do
    putStrLn "Welcome to SPARSE RECAPITALIZATION™."
    putStrLn "© Aidan Ewart, 2021"
    putStr "> runfile "
    hFlush stdout
    filepath <- getLine
    state <- newIORef initialState
    L.run $ do
        --openlibs
        L.registerHaskellFunction "refine" (refineExt state)
        L.registerHaskellFunction "assert" (assertExt state)
        L.registerHaskellFunction "sort" (newSortExt state)
        L.registerHaskellFunction "begin" (beginProofExt state)
        L.registerHaskellFunction "end" (endProofExt state)
        L.dofile filepath
    (_,_,env,_) <- readIORef state
    print env
    pure ()