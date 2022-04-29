module Kuifje.Value where

import qualified Kuifje.Env as E
import qualified Data.Set as DSET
import Language.Kuifje.Distribution

import Text.ParserCombinators.Parsec.Expr

data Value = R Rational 
           | B Bool 
           | T String
           | PD (DSET.Set (Prob, Value))
           | S (DSET.Set Value) 
           | LS [Value]
           deriving (Show, Eq, Ord)

type Gamma = E.Env Value 

