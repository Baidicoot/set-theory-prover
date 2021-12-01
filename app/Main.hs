module Main where
import Frontend
import qualified Foreign.Lua as L
import Data.IORef
import System.IO
import qualified Data.Text as T

initialNames :: [Name]
initialNames = fmap (T.pack . ("v"++) . show) [1..]

main :: IO ()
main = do
    putStrLn "Welcome to SPARSE RECAPITALIZATION™."
    putStrLn "© Aidan Ewart, 2021"
    putStr "> runfile "
    hFlush stdout
    filepath <- getLine
    state <- newIORef (initialState,initialNames)
    L.run $ do
        --openlibs
        L.registerHaskellFunction "refine" (runExt refineExt state)
        L.registerHaskellFunction "assert" (uncurry . runExt assertExt state)
        L.registerHaskellFunction "sort" (runExt newSortExt state)
        L.registerHaskellFunction "beginProof" (runExt beginProofExt state)
        L.registerHaskellFunction "endProof" (runExt endProofExt state)
        L.registerHaskellFunction "const" (uncurry . runExt newConstExt state)
        L.dofile filepath
    (_,_,env,_) <- readIORef state
    print env
    pure ()