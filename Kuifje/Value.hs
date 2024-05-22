module Kuifje.Value where

import qualified Kuifje.Env as E

import Data.List (intercalate)
import Data.Ratio
import qualified Data.Set as S
import Numeric

import Language.Kuifje.Distribution

import Text.ParserCombinators.Parsec.Expr

valueToString :: Value -> String
valueToString (R x) = show x
valueToString (B x) = if x then "TRUE" else "FALSE"
valueToString (T x) = x

data Value = R Double 
           | B Bool 
           | T String
           | PD (S.Set (Prob, Value))
           | S (S.Set Value)
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

isRat :: Value -> Bool
isRat (R _) = True
isRat _ = False

theText :: Value -> String
theText (T s) = s

theSet :: Value -> S.Set Value
theSet (S s) = s

theBool :: Value -> Bool
theBool (B b) = b

theRat :: Value -> Double
theRat (R x) = x

valuePrettyType :: Value -> String
valuePrettyType = vpt
  where
    vpt (R _) = "Rat"
    vpt (B _) = "Bool"
    vpt (T _) = "String"
    vpt (S s) = "Set<" ++ prettyManyTypes (S.toList . S.map vpt $ s) ++ ">"
    vpt (PD s) = "ProbDist<" ++ prettyManyTypes (S.toList . S.map (vpt . snd) $ s) ++ ">"
    vpt (LS vs) = "List<" ++ prettyManyTypes (vpt <$> vs) ++ ">"
    vpt (TP _) = "TP"

    prettyManyTypes :: [String] -> String
    prettyManyTypes s =
      if length s == 1
      then head s
      else intercalate " + " s

-- | Environment / Program state
type Gamma = E.Env Value 

