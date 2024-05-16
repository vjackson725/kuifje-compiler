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

isText :: Value -> Bool
isText (T _) = True
isText _ = False

isSet :: Value -> Bool
isSet (S _) = True
isSet _ = False

isBool :: Value -> Bool
isBool (B _) = True
isBool _ = False

isRational :: Value -> Bool
isRational (R _) = True
isRational _ = False

theText :: Value -> String
theText (T s) = s

theSet :: Value -> DSET.Set Value
theSet (S s) = s

theBool :: Value -> Bool
theBool (B b) = b

theRational :: Value -> Rational
theRational (R x) = x

-- | Environment / Program state
type Gamma = E.Env Value 

