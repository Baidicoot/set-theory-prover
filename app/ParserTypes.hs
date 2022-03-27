{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module ParserTypes where

import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader

import Data.List (intercalate)

import GHC.Generics (Generic)
import Data.Binary (Binary)

data NameLevel
    = Sort
    | Obj
    | Prf
    deriving(Eq,Show)

data NameOrigin
    = Local
    | Global
    | Implicit
    deriving(Show)

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
    | UnknownPlaceholder (S.Set Name)
    | MultiplyBound Name
    deriving(Show)

type ParserGenerator = ExceptT ParseError (State [Name])

type Parser = ExceptT ParseError (ReaderT Grammar (State (V.Vector Tok)))

type Name = T.Text

data Tok
    = Tok TokKind T.Text
    deriving(Eq,Ord,Generic)

instance Binary Tok

instance Show Tok where
    show (Tok k t) = "<" ++ show t ++ "," ++ show k ++ ">"

data TokKind
    = Ident
    | Bracket
    | Symbol
    | Keyword
    | Escaped TokKind
    deriving(Eq,Ord,Show,Generic)

instance Binary TokKind

data Symbol
    = Any TokKind
    | AnyEscaped
    | Exact Tok
    | Nonterminal Name
    deriving(Eq,Ord,Generic)

instance Binary Symbol

instance Show Symbol where
    show (Any k) = "<" ++ show k ++ ">"
    show AnyEscaped = "<Escaped>"
    show (Exact t) = show t
    show (Nonterminal x) = T.unpack x

data NotationBinding
    = BindNonterminal Name Name
    | ExactToken Tok

data SExpr
    = SExpr Name [SExpr]
    | STok Tok
    | SPlaceholder Name
    | Partial TreeRewrite [SExpr]
    deriving(Generic)

instance Binary SExpr

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
    deriving(Show,Generic)

instance Binary TreeRewrite

emptyRule :: ProdRule
emptyRule = (Empty, [])

type Grammar = M.Map Name [ProdRule]

type Keywords = S.Set Name

type ElabCtx = M.Map Name (Name, NameOrigin, NameLevel)