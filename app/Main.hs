{-# LANGUAGE OverloadedStrings #-}
module Main where
import System.IO
import Data.IORef
import System.Environment
import qualified Data.ByteString as B
import RunLua
import Foreign.Lua (dostring,Lua,liftIO,run,openlibs)

promptB :: String -> IO B.ByteString
promptB s = do
  putStr s
  B.getLine

prompt :: String -> IO String
prompt s = do
  putStr s
  getLine

interpreter :: Lua [B.ByteString]
interpreter = do
    state <- liftIO startNewState
    lines <- liftIO (newIORef [])
    openlibs
    loadAPI state
    mainloop lines
    where
        mainloop :: IORef [B.ByteString] -> Lua [B.ByteString]
        mainloop lines = do
            l <- liftIO (promptB "atp> ")
            if l == ":q" then liftIO $ readIORef lines else do
                err <- catchScriptError (dostring l)
                case err of
                    Just err -> liftIO (putStrLn ("ERROR:\n" ++ err))
                    Nothing -> liftIO (modifyIORef' lines (++[l]))
                mainloop lines

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    putStrLn "Welcome to the SPARSE RECAPITALIZATION™ proving system."
    putStrLn "© Aidan Ewart, 2022"
    args <- getArgs
    if null args then do
        lines <- run interpreter
        fp <- prompt "save interactive session to..? (enter to discard) "
        if null fp then pure () else
            B.writeFile fp (B.intercalate "\n" lines)
    else do
        prg <- B.readFile (head args)
        (out,_) <- runProofScript prg
        case out of
            Left err -> putStrLn $ "ERROR:\n" ++ err
            Right env -> do
                putStrLn "\nexited with environment:"
                putStr env