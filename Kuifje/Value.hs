module Kuifje.Value where

import qualified Kuifje.Env as E
import qualified Data.Set as DSET
import Language.Kuifje.Distribution
import Data.Ratio
import Numeric

import Text.ParserCombinators.Parsec.Expr

valueToString :: Value -> String
valueToString (R x) = show (fromRat x)
valueToString (B x) = if x then "TRUE" else "FALSE"
valueToString (T x) = x

data Value = R Rational 
           | B Bool 
           | T String
           | PD (DSET.Set (Prob, Value))
           | S (DSET.Set Value) 
           | LS [Value]
           | TP [Value]
           deriving (Show, Eq, Ord)

type Gamma = E.Env Value 

