module RunLua where

import qualified Foreign.Lua as L
import Data.IORef
import Frontend
import ParserTypes
import qualified Data.ByteString as B
import qualified Data.Text as T

type State = (ProverState,([Name],Maybe Grammar))

catchScriptError :: L.Lua L.Status -> L.Lua (Maybe String)
catchScriptError f = do
    s <- f
    case s of
        L.OK -> pure Nothing
        L.Yield -> pure (Just "YIELDED")
        _ -> do
            err <- L.peek 1
            pure (Just err)

loadAPI :: IORef State -> L.Lua ()
loadAPI state = do
    L.registerHaskellFunction "refine" (runExt "refine" refineExt state)
    L.registerHaskellFunction "assert" (curry $ runExt "assert" assertExt state)
    L.registerHaskellFunction "sort" (runExt "sort" newSortExt state)
    L.registerHaskellFunction "beginProof" (runExt "beginProof" beginProofExt state)
    L.registerHaskellFunction "endProof" (runExt "endProof" endProofExt state)
    L.registerHaskellFunction "const" (curry $ runExt "const" newConstExt state)
    L.registerHaskellFunction "keyword" (runExt "keyword" newKeywordExt state)
    L.registerHaskellFunction "notation" (curry $ runExt "notation" notationExt state)
    L.registerHaskellFunction "die" (runActionExt "die" dieExt state)
    L.registerHaskellFunction "printGrammar" (runActionExt "printGrammar" printGrammarExt state)
    L.registerHaskellFunction "done" (runActionExt "done" doneExt state)
    L.registerHaskellFunction "loadState" (runExt "loadState" loadStateExt state)
    L.registerHaskellFunction "includeState" (runExt "includeState" loadStateExt state)
    L.registerHaskellFunction "dumpState" (runOutputExt "dumpState" dumpStateExt state)
    L.registerHaskellFunction "define" (curry $ runExt "define" defineExt state)

runLuaWithProver :: IORef State -> L.Lua L.Status -> IO (Maybe String)
runLuaWithProver state lua = L.run $ do
    L.openlibs
    loadAPI state
    catchScriptError lua

initialNames :: [Name]
initialNames = fmap (T.pack . ("v"++) . show) [1..]

startNewState :: IO (IORef State)
startNewState = newIORef (initialState,(initialNames,Nothing))

runProofScript :: B.ByteString -> IO (Either String String, IORef State)
runProofScript prg = do
    state <- startNewState
    err <- runLuaWithProver state (L.dostring prg)
    case err of
        Just err -> pure (Left err,state)
        Nothing -> do
            ((_,_,env,_),_) <- readIORef state
            pure (Right $ showEnv env,state)