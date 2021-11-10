module Frontend where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef
import Foreign.Ptr

import Kernel

newtype ConstObjs = ConstObjs (M.Map Name Monotype)
newtype DefinedObjs = DefObjs (M.Map Name (Monotype,DeBrujin))
newtype ConstSorts = Sorts (S.Set Name)
newtype Axioms = Axioms (M.Map Name DeBrujin)
type Env = (ConstSorts, ConstObjs, DefObjs, Axioms)