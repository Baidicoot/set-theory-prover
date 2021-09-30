module Grammar where

import qualified Data.Text as T
import qualified Data.Vector as V

newtype Tok = Tok T.Text

data GrammarTerm
    = Symbol T.Text
    | Parameter T.Text

data GrammarRule
    = Rule [GrammarTerm] [GrammarTerm]