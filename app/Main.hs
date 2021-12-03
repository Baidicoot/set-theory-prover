module Main where
import Frontend
import qualified Foreign.Lua as L
import Data.IORef
import System.IO
import qualified Data.Text as T
import ParserTypes

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
        L.registerHaskellFunction "assert" (curry $ runExt assertExt state)
        L.registerHaskellFunction "sort" (runExt newSortExt state)
        L.registerHaskellFunction "beginProof" (runExt beginProofExt state)
        L.registerHaskellFunction "endProof" (runExt endProofExt state)
        L.registerHaskellFunction "const" (curry $ runExt newConstExt state)
        L.dofile filepath
    ((_,env,_),_) <- readIORef state
    print env
    pure ()