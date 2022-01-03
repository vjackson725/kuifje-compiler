module Kuifje.Value where

import qualified Kuifje.Env as E
import qualified Data.Set as DSET

import Text.ParserCombinators.Parsec.Expr

data Value = R Rational 
           | B Bool 
           | T String
           | S (DSET.Set Value) 
           deriving (Show, Eq, Ord)

type Gamma = E.Env Value 

