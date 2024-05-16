{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.LivenessAnalysis where

import qualified Kuifje.Env as E
import qualified Data.Map as Map
import Kuifje.Value
import Kuifje.Parse
import Kuifje.Syntax
import Kuifje.Expr
import Kuifje.Stmt

import Control.Lens hiding (Profunctor)
import Data.Semigroup
import Data.Ratio
import Data.Map.Strict
import Data.List
import qualified Data.Set as DSET
import Numeric

import Language.Kuifje.Distribution
--import Kuifje.PrettyPrint 
import Language.Kuifje.PrettyPrint
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Control.Applicative

import System.IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

checkListInMap :: Map.Map String Expr -> [String] -> Bool
checkListInMap m [] = True
checkListInMap m ls =
        let hd = Map.member (head ls) m
            tl = checkListInMap m (tail ls)
         in if hd == False then
            error ("\n\n  Variable (" ++ (head ls) ++ ") not declared before being used.")
           else (hd && tl)

livenessAnalysis :: MonadValue -> Map.Map String Expr -> (Bool, Map.Map String Expr)
livenessAnalysis (M m) vars = (True, vars)
livenessAnalysis (O e) vars = ((checkListInMap vars (recoverVars e [])),vars)
livenessAnalysis (A id e) vars =
        let newVars = Map.insert id e vars
            varList = recoverVars e []
            valid = checkListInMap vars varList
         in (valid, newVars)
livenessAnalysis (L []) vars = (True, vars)
livenessAnalysis (L ls) vars =
        let (hdVal, hdVars) = livenessAnalysis (head ls) vars
            (tlVal, tlVars) = livenessAnalysis (L (tail ls)) hdVars
         in ((hdVal && tlVal), tlVars)
livenessAnalysis (C e t f) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (tVal, _) = livenessAnalysis t vars
            (fVal, _) = livenessAnalysis f vars
         in ((eVal && tVal && fVal), vars)
livenessAnalysis (E t f e) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (tVal, tVars) = livenessAnalysis t vars
            (fVal, fVars) = livenessAnalysis f tVars
         in ((eVal && tVal && fVal), fVars)
livenessAnalysis (W e b) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (bVal, bVars) = livenessAnalysis b vars
         in ((eVal && bVal), vars)

runLivenessAnalysis :: MonadValue -> Bool
runLivenessAnalysis m = if (fst (livenessAnalysis m Map.empty)) == False
                        then error ("\n\nInvalid Program. Use of undeclared variable.\n No debug information found.\n")
                        else True

