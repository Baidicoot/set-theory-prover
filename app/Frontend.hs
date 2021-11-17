module Frontend where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef
import Foreign.Ptr

import Kernel

import qualified Foreign.Lua as Lua

newtype ConstObjs = ConstObjs (M.Map Name Monotype)
newtype DefinedObjs = DefObjs (M.Map Name (Monotype,DeBrujin))
newtype ConstSorts = Sorts (S.Set Name)
newtype Axioms = Axioms (M.Map Name DeBrujin)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)

-- environment, current proof (if applicable)
type State = (Env, Maybe Proof)

refine :: State -> Proof -> Lua State

parseProof :: State -> Text -> Lua Proof

parseSort :: State -> Text -> Lua Monotype

parseProp :: State -> Text -> Lua Term

parseProd :: State -> Text -> Text -> Lua ProdRule

refineExt :: IORef State -> Text -> Lua ()

assertExt :: IORef State -> Text -> Text -> Lua ()

newSortExt :: IORef State -> Text -> Lua ()

notationExt :: IORef State -> Text -> Text -> Lua ()

{- references to IORef through CLOSURES! -}

{-
-- i.e.
main = do
    x <- newIORef mempty
    Lua.registerHaskellFunction "reduce" (reduce x)
-}