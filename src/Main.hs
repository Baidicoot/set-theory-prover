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
        Right (e,s') -> do
            writeIORef state s'
            case e of
                Just e -> putStrLn (e ++ "\n")
                Nothing -> pure ()
        Left e -> putStrLn (e ++ "\n")

ldFile :: IORef CommandState -> String -> IO ()
ldFile st f = readFile f >>= doLines st

repl :: [String] -> IORef CommandState -> IO ()
repl files state = do
    l <- trim <$> prompt "att> "
    case l of
        ":q" -> putStrLn "Goodbye!"
        ":r" -> writeIORef state emptyState
            >> mapM_ (ldFile state) files
            >> repl files state
        (':':'u':xs) -> repl (filter (/= trim xs) files) state
        (':':'l':xs) -> do
            ldFile state (trim xs)
            repl (trim xs:files) state
        _ -> doLines state l >> repl files state

main :: IO ()
main = newIORef emptyState >>= repl []
