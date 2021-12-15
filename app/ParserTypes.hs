{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module ParserTypes where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import Data.List (intercalate)

data NameLevel
    = Sort
    | Obj
    | Prf
    deriving(Eq,Show)

data NameOrigin
    = Local
    | Global
    | Implicit

data ParseError
    = NotNonterminal Name
    | NotTerminal Name
    | NoMatch Symbol Tok
    | NoSExpr [SExpr]
    | EndOfInput
    | LeftoverInput (V.Vector Tok)
    | EmptyAlternative
    | ElabError SExpr String
    | ScopeError Name
    | NamespaceError Name NameLevel NameLevel
    deriving(Show)

type ParserGenerator = ExceptT ParseError (State [Name])

type Parser = ExceptT ParseError (ReaderT Grammar (State (V.Vector Tok)))

type Name = T.Text

data Tok
    = Tok TokKind T.Text
    deriving(Eq,Ord)

instance Show Tok where
    show (Tok k t) = "<" ++ show t ++ "," ++ show k ++ ">"

data TokKind
    = Ident
    | Bracket
    | Symbol
    | Escaped TokKind
    deriving(Eq,Ord,Show)

data Symbol
    = Any TokKind
    | AnyEscaped
    | Exact Tok
    | Nonterminal Name
    deriving(Eq,Ord)

instance Show Symbol where
    show (Any k) = "<" ++ show k ++ ">"
    show AnyEscaped = "<Escaped>"
    show (Exact t) = show t
    show (Nonterminal x) = T.unpack x

data NotationError
    = UnknownPlaceholder (S.Set Name)
    | MultiplyBound Name
    deriving(Show)

data NotationBinding
    = BindNonterminal Name Name
    | ExactToken Tok

data SExpr
    = SExpr Name [SExpr]
    | STok Tok
    | SPlaceholder Name
    | Partial TreeRewrite [SExpr]

instance Show SExpr where
    show (STok t) = show t
    show (SExpr t xs) = "(" ++ show t ++ " " ++ unwords (fmap show xs) ++ ")"
    show (SPlaceholder n) = "`" ++ show n ++ "`"
    show (Partial _ xs) = "(partial " ++ unwords (fmap show xs) ++ ")"

type ProdRule
    = (TreeRewrite, [Symbol])

data TreeRewrite
    = Subst [Maybe Name] SExpr
    | Single
    | Empty
    | Placeholder
    | RawSExpr
    | ListCons Name
    | ListNull Name
    | Combine Int TreeRewrite TreeRewrite
    | RewritePartial TreeRewrite
    | ConstructPartial TreeRewrite
    deriving(Show)

emptyRule :: ProdRule
emptyRule = (Empty, [])

type Grammar = M.Map Name [ProdRule]

type ElabCtx = M.Map Name (Name, NameOrigin, NameLevel)