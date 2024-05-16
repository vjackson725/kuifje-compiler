{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Translator where 

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

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

trd3 :: (a, b, c) -> c
trd3 (_, _, x) = x

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

snd4 :: (a, b, c, d) -> b
snd4 (_, x, _, _) = x

trd4 :: (a, b, c, d) -> c
trd4 (_, _, x, _) = x

frt4 :: (a, b, c, d) -> d
frt4 (_, _, _, x) = x

recoverListLength :: Expr -> Expr
recoverListLength (Var idList) = (ListLength (Var idList))
recoverListLength (ListExpr list) = (RationalConst (toRational (length list)))

recoverListID :: Expr -> Expr -> Expr
recoverListID (Var idList) index = (ListElem idList index)
recoverListID (ListExpr list) index = (ListElemDirect list index)

recoverAsgn :: Expr -> Stmt ->  Map.Map String (Stmt, [String], [Expr]) -> Map.Map String Expr -> MonadValue -> (MonadValue, Map.Map String (Stmt, [String], [Expr]), Map.Map String Expr)
recoverAsgn (CallExpr name params) (Assign id expr) fBody fCntx list =
        let base = (getFuncBody name fBody)
            baseStmt = fst3 base
            fInput = snd3 base
            fOutput = trd3 base
            baseUpdated = updateStmtUses name baseStmt
            outCntxStmt = addOutputCntx name fOutput id baseUpdated
            inCntxStmt = addInputCntx name fInput params outCntxStmt
         --in error ("Call is:\n" ++ (show inCntxStmt))
         in translateExecKuifje inCntxStmt fBody fCntx list
recoverAsgn _ (Assign id expr) fBody fCntx list =
        let newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)

translateExecKuifje :: Stmt -> Map.Map String (Stmt, [String], [Expr]) -> Map.Map String Expr -> MonadValue -> (MonadValue, Map.Map String (Stmt, [String], [Expr]), Map.Map String Expr)
-- Sequence Statements
translateExecKuifje (Seq []) fBody fCntx list = (list, fBody, fCntx)
translateExecKuifje (Seq ls) fBody fCntx list = 
        let (hdRes, hdFBody, hdFCntx) = (translateExecKuifje (head ls) fBody fCntx list)
            (tlRes, tlFBody, tlFCntx) = (translateExecKuifje (Seq (tail ls)) hdFBody hdFCntx hdRes)
         in (translateExecKuifje (Seq (tail ls)) hdFBody hdFCntx hdRes)
-- Assign Statements
translateExecKuifje (Assign id expr) fBody fCntx list = recoverAsgn expr (Assign id expr) fBody fCntx list
--translateExecKuifje (Assign id expr) fBody fCntx list = 
--        let newFCntx = Map.insert id expr fCntx
--            monadList = concatMonadValues list (A id expr)
--         in (monadList, fBody, newFCntx)
-- Support Statements
translateExecKuifje (Plusplus id) fBody fCntx list = 
        let var = (Var id)
            one = (RationalConst 1)
            expr = (ABinary Add var one)
         in recoverAsgn expr (Assign id expr) fBody fCntx list
translateExecKuifje (Lessless id) fBody fCntx list = 
        let var = (Var id)
            one = (RationalConst 1)
            expr = (ABinary Subtract var one)
         in recoverAsgn expr (Assign id expr) fBody fCntx list
translateExecKuifje (Support id (Var idexp)) fBody fCntx list = 
        let gammaL = createMonnad list
            kuifje = hysem gammaL (uniform [E.empty])
            executed = exec idexp kuifje
            support = getSupportFromHyper executed
            dist = recoverSupportAsDistList support
         in if ((length dist) == 1)
            then let setExpr = valueToExpr (snd (convertTuple (head dist)))
                     (newRes, newFBody, newFCntx) = translateExecKuifje (Assign id setExpr) fBody fCntx list
                  in (newRes, newFBody, newFCntx)
            else let setExpr = (INUchoices dist)
                     (newRes, newFBody, newFCntx) = translateExecKuifje (Assign id setExpr) fBody fCntx list
                  in (newRes, newFBody, newFCntx)
translateExecKuifje (Support id exp) fBody fCntx list =
        let distName = "DIST." ++ id
            (newRes, newFBody, newFCntx) = translateExecKuifje (Assign distName exp) fBody fCntx list
         in translateExecKuifje (Support id (Var distName)) newFBody newFCntx newRes
-- Function Statements
translateExecKuifje (FuncStmt name body lInput) fBody fCntx list =
        let (Seq insts) = body
            lOutput = findReturns insts
            nMap = Map.insert name (body, lInput, lOutput) fBody
            stmt = fst3 (translateExecKuifje (Kuifje.Syntax.Skip) fBody fCntx list)
            monadList = concatMonadValues list stmt
         in (monadList, nMap, fCntx)
-- Return Statements
--   Returns were processed by FuncStmt, and should be skiped at this point:
translateExecKuifje (ReturnStmt outputs) fBody fCntx list = (list, fBody, fCntx)
translateExecKuifje (Kuifje.Syntax.If e s1 s2) fBody fCntx list =
        let listTrue = (fst3 (translateExecKuifje s1 fBody fCntx (L [])))
            listFalse = (fst3 (translateExecKuifje s2 fBody fCntx (L [])))
            (newRes, newFBody, newFCntx) = ((C e listTrue listFalse), fBody, fCntx)
            monadList = concatMonadValues list newRes
         in (monadList, newFBody, newFCntx)
-- While Statements
translateExecKuifje (Kuifje.Syntax.While e body) fBody fCntx list =
        -- If a variable controls a loop, it is leaked to the adversary:
        let (lBody, newFBody, newFCntx) = translateExecKuifje body fBody fCntx (O e)
            monadList = concatMonadValues list (W e lBody)
         in (monadList, newFBody, newFCntx)
-- For Statements
--translateExecKuifje (For index (Var idList) body) fBody fCntx list = 
translateExecKuifje (For index ls body) fBody fCntx list =
        let iteratorID = "iterator." ++ index
            listLen = recoverListLength ls--(ListLength (Var idList))

            preCond = concatMonadValues list (A iteratorID (RationalConst (0 % 1)))
            cond = (RBinary Lt (Var iteratorID) listLen)
            postCond = (ABinary Add (Var iteratorID) (RationalConst (1 % 1)))
            
            --element = (ListElem idList (Var iteratorID))
            element = recoverListID ls (Var iteratorID)
            toAppend = [(A index element)] ++ [(A iteratorID postCond)]
            (lBody, newFBody, newFCntx) = translateExecKuifje body fBody fCntx (L toAppend)
            monadList = concatMonadValues preCond (W cond lBody)
         in (monadList, newFBody, newFCntx)
-- Skip Statements
translateExecKuifje Kuifje.Syntax.Skip fBody fCntx list = ((concatMonadValues list (M skip)), fBody, fCntx)
-- Leak Statements
translateExecKuifje (Leak e) fBody fCntx list = ((concatMonadValues list (O e)), fBody, fCntx)
-- Vis Statements
translateExecKuifje (Vis s) fBody fCntx list = ((concatMonadValues list (M undefined)), fBody, fCntx)
-- External Choice Statements
translateExecKuifje (Echoice s1 s2 p) fBody fCntx list = 
        let listTrue = (fst3 (translateExecKuifje s1 fBody fCntx (L [])))
            listFalse = (fst3 (translateExecKuifje s2 fBody fCntx (L [])))
            (newRes, newFBody, newFCntx) = ((E listTrue listFalse p), fBody, fCntx)
            monadList = concatMonadValues list newRes
         in (monadList, newFBody, newFCntx)
-- Sampling Statements
translateExecKuifje (Sampling id (Var idexp)) fBody fCntx list =
        let exprD = getCntxExpr idexp fCntx
            expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)
translateExecKuifje (Sampling id exprD) fBody fCntx list =
        let expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)
-- Default Value - Case a Statement is not found
translateExecKuifje stmt _ _ list = error ("Invalid Statement:\n" ++ (show stmt) ++ "\nList:\n" ++ (monadType list))

project :: Dist (Dist Gamma) -> Dist (Dist Rational)
project = fmapDist (fmapDist (\s -> getRational s "y"))

initGamma :: Rational -> Rational -> Gamma
initGamma x y = let g = E.add E.empty ("x", (R x)) in 
               E.add g ("y", (R y))

hyper :: Dist (Dist Rational)
hyper = let g = createMonnad (fst3 (translateExecKuifje exampelS Map.empty Map.empty (L [])))
         in project $ hysem g (uniform [E.empty])

example :: String
example = "y := 0; while (x > 0) do y := x + y; x := x - 1; od;"

exampelS :: Stmt
exampelS = let (Seq ls) = parseString example 
            in Seq $ (Assign "x" (Ichoice
                        (RationalConst (5 % 1)) 
                        (RationalConst (6 % 1)) 
                        (RationalConst (1 % 2)) )):ls
