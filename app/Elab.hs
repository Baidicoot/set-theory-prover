{-# LANGUAGE OverloadedStrings #-}
module Elab where

import Kernel
import ParserTypes

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

{- elaboration of parse trees into Kernel.Types structures -}

type ElabCtx = _

type Elaborator = ReaderT ElabCtx (State [Name])

fresh :: Elaborator Name
fresh = do
    ns <- get
    let (x:xs) = ns
    put xs
    pure x

elabSort :: SExpr -> Elaborator Monotype
elabSort (SExpr "func" [x,y]) = liftM2 Arr (elabSort x) (elabSort y)
elabSort (SExpr "prop" []) = pure Prop