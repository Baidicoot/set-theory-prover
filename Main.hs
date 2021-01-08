module Main where

import Command (CommandState)
import Parser (interpret,trim)
import System.IO
import Control.Monad.Except
import Control.Monad.Writer
import Data.IORef

prompt :: String -> IO String
prompt text = do
    putStr text
    hFlush stdout
    getLine

doLines :: IORef CommandState -> String -> IO ()
doLines state l = do
    s <- readIORef state
    let (t,log) = runWriter (runExceptT (interpret l s))
    case t of
        Right (out,s') -> do
            writeIORef state s'
            mapM_ print out
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
main = newIORef ([] :: CommandState) >>= repl
