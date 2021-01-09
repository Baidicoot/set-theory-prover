module Main where

import Command (CommandState,emptyState)
import Parser (interpret,trim)
import TT (runRes,Universe)
import System.IO
import Control.Monad.Except
import Control.Monad.Writer
import Data.IORef

prompt :: String -> IO String
prompt text = do
    putStr text
    hFlush stdout
    getLine

doLines :: IORef (CommandState,Universe) -> String -> IO ()
doLines state l = do
    (s,u) <- readIORef state
    let (t,log) = runRes u (interpret l s)
    case t of
        Right ((out,s'),u') -> do
            mapM_ print out
            writeIORef state (s',u')
        Left e -> putStrLn (e ++ "\n")

repl :: IORef (CommandState,Universe) -> IO ()
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
main = newIORef (emptyState,0) >>= repl
