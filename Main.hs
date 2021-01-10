module Main where

import Command (CommandState,emptyState)
import Parser (interpret,trim)
import TT (runRes,Universe)
import System.IO
import Control.Monad.Except
import Data.IORef

prompt :: String -> IO String
prompt text = do
    putStr text
    hFlush stdout
    getLine

doLines :: IORef CommandState -> String -> IO ()
doLines state l = do
    s <- readIORef state
    case runExcept (interpret l s) of
        Right (out,s') -> do
            mapM_ print out
            writeIORef state s'
        Left e -> putStrLn (e ++ "\n")

repl :: IORef CommandState -> IO ()
repl state = do
    l <- trim <$> prompt "att> "
    case l of
        ":q" -> putStrLn "Goodbye!"
        (':':'l':xs) -> do
            ls <- readFile (trim xs)
            doLines state ls
            repl state
        _ -> doLines state l >> repl state

main :: IO ()
main = newIORef emptyState >>= repl
