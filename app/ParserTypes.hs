{-# LANGUAGE LambdaCase #-}
module ParserTypes where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

data ParseError
    = NotNonterminal Name
    | NotTerminal Name
    | NoMatch Symbol Tok
    | NoSExpr [SExpr]
    | EndOfInput
    | EmptyAlternative

type ParserGenerator = ExceptT ParseError (State [Name])

type Parser = ExceptT ParseError (ReaderT Grammar (State (V.Vector Tok)))

type Name = T.Text

data Tok
    = Tok TokKind T.Text
    deriving(Eq,Ord)

data TokKind
    = Ident
    | Oper
    deriving(Eq,Ord)

data Symbol
    = Any TokKind
    | Exact Tok
    | Nonterminal Name
    deriving(Eq,Ord)

type TreeRewrite = [SExpr] -> Maybe SExpr

data SExpr
    = SExpr Tok [SExpr]
    | Partial TreeRewrite [SExpr]

data ProdRule
    = Prod TreeRewrite [Symbol]

emptyRule :: ProdRule
emptyRule = Prod (const (Just (Partial f []))) []
    where
        f [x] = Just x
        f _ = Nothing

type Grammar = [(Name,[ProdRule])]