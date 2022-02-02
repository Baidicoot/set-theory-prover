{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module PrettyPrint where

import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Vector as V
import Data.List
import Data.Char

import Kernel.Types hiding(Name)
import ParserTypes
import Errors

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
    showWith (Polytype xs t) x
        | S.null xs = showWith t x
        | otherwise = "∀" ++ intercalate "," (T.unpack <$> S.toList xs)
                ++ ", " ++ showWith t x

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

instance Showable Tok ShowCtx where
    showWith (Tok _ n) _ = "'" ++ T.unpack n ++ "'"

instance Showable Symbol ShowCtx where
    showWith (Exact t) x = showWith t x
    showWith (Nonterminal n) _ = T.unpack n
    showWith AnyEscaped _ = "_@Escaped"
    showWith (Any k) _ = "_@" ++ show k

instance Showable SExpr ShowCtx where
    showWith (STok t) x = showWith t x
    showWith (SExpr t xs) x = "(" ++ T.unpack t ++ " " ++ unwords (fmap (`showWith` x) xs) ++ ")"
    showWith (SPlaceholder n) x = "`" ++ T.unpack n ++ "`"
    showWith (Partial _ xs) x = "(partial " ++ unwords (fmap (`showWith` x) xs) ++ ")"

instance Showable ParseError ShowCtx where
    showWith (NotNonterminal n) _ = "unknown nonterminal " ++ T.unpack n
    showWith (NotTerminal n) _ = "unknown terminal " ++ T.unpack n
    showWith (NoMatch s t) x = "got " ++ showWith t x ++ ", expected" ++ showWith s x
    showWith (NoSExpr s) x = "could not parse " ++ unwords (fmap (`showWith` x) s)
    showWith EndOfInput x = "got end of input"
    showWith (LeftoverInput xs) x = "got leftover input " ++ unwords ((`showWith` x) <$> V.toList xs)
    showWith EmptyAlternative x = "no rules to parse"
    showWith (ElabError s n) x = "expected " ++ n ++ " got " ++ showWith s x
    showWith (ScopeError n) x = "name " ++ T.unpack n ++ " not in scope"
    showWith (NamespaceError n r a) x = "expected " ++ show r ++ " but " ++ T.unpack n ++ " is " ++ show a
    showWith (UnknownPlaceholder ns) x = "unknown placeholder(s) " ++ intercalate ", " (T.unpack <$> S.toList ns)
    showWith (MultiplyBound n) x = "placeholder " ++ T.unpack n ++ " is multiply bound"

instance Showable NormalError ShowCtx where
    showWith NotInProofMode x = "not in proof mode"
    showWith InProofMode x = "in proof mode"
    showWith NoOpenGoals x = "no open goals"
    showWith OpenGoals x = "open goals"
    showWith Terminated x = "typechecker exited by user"
    showWith (Parser e) x = showWith e x
    showWith (Checker e) x = showWith e x
    showWith (Serializer s) x = s

instance Showable NormalTrace ShowCtx where
    showWith (CallingFunc n) x = "calling function '" ++ n ++ "'"
    showWith (CheckerT e) x = showWith e x

instance Showable ProofTrace ShowCtx where
    showWith (CheckingProof p t) x = "checking" ++ showLine (x+2) ++ showWith p (x+2)
        ++ "\nhas type" ++ showLine (x+2) ++ showWith t (x+2)
    showWith (CheckingTerm p t) x = "checking" ++ showLine (x+2) ++ showWith p (x+2)
        ++ "\nhas type" ++ showLine (x+2) ++ showWith t (x+2)
    showWith (InferringProof p) x = "inferring type of" ++ showLine (x+2) ++ showWith p (x+2)
    showWith (InferringTerm p) x = "inferring type of" ++ showLine (x+2) ++ showWith p (x+2)

showDefs :: (Showable a ShowCtx) => M.Map Name a -> ShowCtx -> String
showDefs m x = intercalate "\n" $
    (\(n,d) -> T.unpack n ++ " :: " ++ showWith d x) <$> M.toList m