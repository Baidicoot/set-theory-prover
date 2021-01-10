module Main where

import Command (CommandState,emptyState,runCmd)
import Parser (interpret,trim)
import System.IO
import Data.IORef

prompt :: String -> IO String
prompt text = do
    putStr text
    hFlush stdout
    getLine

doLines :: IORef CommandState -> String -> IO ()
doLines state l = do
    s <- readIORef state
    let (r,out) = runCmd (interpret l s)
    mapM_ print out
    case r of
        Right s' -> writeIORef state s'
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
