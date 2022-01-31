{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Showable where

import qualified Data.Text as T
import qualified Data.Set as S
import Data.List
import Data.Char

import Kernel.Types

class Showable t c where
    showWith :: t -> c -> String

type ShowCtx = Int

showWithBracket :: (Showable t c) => t -> c -> String
showWithBracket t c =
    let s = showWith t c
    in if any isSpace s then
        "(" ++ s ++ ")"
    else s

showLine :: Int -> String
showLine n = '\n':replicate n ' '

instance Showable Monotype ShowCtx where
    showWith (TyVar n) x = T.unpack n
    showWith (Arr a b) x = showWithBracket a x ++ " -> " ++ showWith b x
    showWith (ConstTy n) x = T.unpack n
    showWith Prop x = "Prop"

instance Showable Polytype ShowCtx where
    showWith (Polytype xs t) x = "∀" ++ intercalate "," (show <$> S.toList xs) ++ ", "
        ++ showWith t x

instance Showable Term ShowCtx where
    showWith (Lam n b) x = "λ" ++ T.unpack n ++ ", " ++ showWith b (x+2)
    showWith (Let n e b) x = "let " ++ T.unpack n ++ " = "
        ++ showWith e (x+2) ++ " in" ++ showLine x ++ showWith b (x+2)
    showWith (App a b) x = showWith a x ++ " " ++ showWithBracket b x
    showWith (Imp a b) x = showWithBracket a x ++ " => " ++ showWith b x
    showWith (Forall n t e) x = "∀" ++ T.unpack n ++ ": " ++ showWith t x
        ++ ", " ++ showWith e (x+2)
    showWith (MetaVar n) x = '?':T.unpack n
    showWith (Var n) x = T.unpack n

instance Showable Proof ShowCtx where
    showWith (ModPon a b) x = showWith a x ++ " " ++ showWith b x
    showWith (IntroThm n t p) x = "introThm " ++ T.unpack n ++ ": "
        ++ showWith t x ++ "," ++ showLine x ++ showWith p (x+2)
    showWith (IntroObj n t p) x = "introObj " ++ T.unpack n ++ ": "
        ++ showWith t x ++ "," ++ showLine x ++ showWith p (x+2)
    showWith (UniElim p t) x = "subst " ++ showWith t (x+2) ++ "in"
        ++ showLine x ++ showWith p x
    showWith (Axiom n) x = T.unpack n
    showWith Hole x = "_"

instance Showable ProofError ShowCtx where
    showWith (InfiniteType n m) x = "cannot construct infinite type "
        ++ T.unpack n ++ " ~ " ++ showWith m x
    showWith (MonotypeUnificationFail n m) x = "cannot unify the types "
        ++ showWith n x ++ " ~ " ++ showWith m x
    showWith (PolytypeUnificationFail n m) x = "cannot unify the types "
        ++ showWith n x ++ " ~ " ++ showWith m x
    showWith (NotInContext n) x = "unknown name " ++ T.unpack n
    showWith (ObjectUnificationFail n m) x = "cannot unify the props "
        ++ showWith n x ++ " ~ " ++ showWith m x
    showWith (HigherOrderUnification n m) x = "cannot perform the higher-order unification "
        ++ showWith n x ++ " ~ " ++ showWith m x
    showWith (NonFunctionEval n) x = "cannot evaluate non-function " ++ showWith n x
    showWith (NoEvalRule n) x = "cannot evaluate " ++ showWith n x
    showWith (DoesNotMatch n m) x = "expression " ++ showWith n x
        ++ " does not have type " ++ showWith m x
    showWith (NotForall n m) x = "expression " ++ showWith n x
        ++ " does not have type " ++ showWith m x
    showWith (UnknownAxiom n) x = "unknown name " ++ T.unpack n
    showWith (CantInferHigherOrder n m) x = "cannot infer type of " ++ T.unpack n
        ++ " in " ++ showWith m x