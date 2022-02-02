module Errors where

import Control.Exception

import Kernel.Types
import ParserTypes (ParseError)

data NormalError
    = NotInProofMode
    | InProofMode
    | NoOpenGoals
    | OpenGoals
    | Terminated
    | Parser ParseError
    | Checker ProofError
    | Serializer String
    deriving(Show)

data NormalTrace
    = CallingFunc String
    | CheckerT ProofTrace
    deriving(Show)