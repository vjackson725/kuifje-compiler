{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.CsvLoader where

import System.Environment
import System.IO
import System.IO.Unsafe
import Data.IORef
import Data.Ratio
import qualified Data.Char as Ch

import Kuifje.Value
import Kuifje.Syntax

import Text.PrettyPrint.Boxes
import qualified Data.Set as S
import qualified Data.Map as M
import Numeric
import qualified Data.List as L
--import Language.Kuifje.PrettyPrint
import Language.Kuifje.Distribution

import Kuifje.Env

-------------------------------------------------------------------------------
--                         General Functions
-------------------------------------------------------------------------------

--loadCSVs Stmt -> IO Stmt
--loadCSVs (Csv identifier file columns filter) = do program <- readFile file
--                                                   case parse statements "" program of
--                                                        Left e  -> print e >> fail "parse error"
--                                                        Right r -> return r

wordsWhen     :: (Char -> Bool) -> String -> [String]
wordsWhen p s =  case dropWhile p s of
                      "" -> []
                      s' -> w : wordsWhen p s''
                            where (w, s'') = break p s'

convertExprLsToText :: [Expr] -> String
convertExprLsToText [] = ""
convertExprLsToText ls = let hd = exprToStr (head ls)
                             tl = convertExprLsToText (tail ls)
                          in (hd ++ tl)
                             
isStrRational :: String -> Bool
isStrRational "" = True
isStrRational s = let hd = head s
                   in if ((Ch.isDigit hd) || (hd == '.'))
                      then (isStrRational (tail s))
                      else False

convertStrToRational :: String -> Rational
convertStrToRational s = toRational (read s :: Float)

selectCols :: String -> Integer -> [Integer] -> [String] -> [Expr]
selectCols _ _ [] [] = []
selectCols "Set" id cols val = let hdCols = head cols
                          in if id == hdCols
                             then let hdVal = head val
                                      tlCols = tail cols
                                      tlVal = tail val
                                      tl = selectCols "Set" (id+1) tlCols tlVal
                                   in ((Text hdVal) : tl)
                             else (selectCols "Set" (id+1) cols (tail val))
selectCols "Text" id cols val = let hdCols = head cols
                          in if id == hdCols
                             then let hdVal = head val
                                      tlCols = tail cols
                                      tlVal = tail val
                                      tl = convertExprLsToText (selectCols "Text" (id+1) tlCols tlVal)
                                   in if (length cols) == 1
                                      then [(Text hdVal)]
                                      else [(Text (hdVal ++ "," ++ tl))]
                             else (selectCols "Text" (id+1) cols (tail val))
selectCols "Type" id cols val = let hdCols = head cols
                          in if id == hdCols
                             then let hdVal = head val
                                      tlCols = tail cols
                                      tlVal = tail val
                                      tl = selectCols "Type" (id+1) tlCols tlVal
                                   in if (isStrRational hdVal)
                                      then ((RationalConst (convertStrToRational hdVal)) : tl)
                                      else ((Text hdVal) : tl)
                             else (selectCols "Type" (id+1) cols (tail val))


createExpressions :: String -> Integer -> [Integer] -> [String] -> [Expr]
createExpressions _ _ _ [] = []
createExpressions "Text" _ cols ls = let hd = head ls
                                         tl = createExpressions "Text" 0 cols (tail ls)
                                         cl = wordsWhen (==',') hd
                                         vals = selectCols "Text" 0 cols cl
                                      in (head vals) : tl 
createExpressions "Unique Text" id cols ls = let hd = head ls
                                                 tl = createExpressions "Unique Text" (id + 1) cols (tail ls)
                                                 cl = wordsWhen (==',') hd
                                                 (Text vals) = head (selectCols "Text" 0 cols cl)
                                                 uVal = (show id) ++ "," ++ vals
                                              in (Text uVal) : tl
createExpressions tpy _ cols ls = let hd = head ls
                                      tl = createExpressions tpy 0 cols (tail ls)
                                      cl = wordsWhen (==',') hd
                                      vals = selectCols tpy 0 cols cl
                                      set = S.fromList vals
                                   in (Eset set) : tl

limitList :: Integer -> [Expr] -> [Expr]
limitList 0 ls = ls
limitList n ls = if (n-1) == 0
                 then [(head ls)]
                 else (head ls) : (limitList (n-1) (tail ls))

exprToStr :: Expr -> String
exprToStr (Text t) = t
exprToStr e = error ("Invalid Filename:\n  " ++ (show e))

lExprTolValues :: [Expr] -> [Value]
lExprTolValues [] = []
lExprTolValues ls =
        let hd = exprToValue (head ls)
            tl = lExprTolValues (tail ls)
         in hd : tl

exprToValue :: Expr -> Value
exprToValue (RationalConst r) = (R r)
exprToValue (Text t) = (T t)
exprToValue (Neg a) = exprToValue (ABinary Multiply (RationalConst (-1 % 1)) a)
exprToValue (BoolConst b) = (B b)
exprToValue (ABinary Multiply (RationalConst a) (RationalConst b)) = (R (a * b))
exprToValue (ABinary Divide (RationalConst a) (RationalConst b)) = (R (a / b))
exprToValue (Eset ns) =
   let e = S.elems ns
       l = lExprTolValues e
       s = S.fromList l
    in (S s)
exprToValue (IchoiceDist e1 e2 p) =
   let v1 = exprToValue e1
       v2 = exprToValue e2
       (R r) = exprToValue p
       p2 = (1 - r)
       list = [(Prob r, v1), (Prob p2, v2)]
    in (PD (S.fromDistinctAscList list))
exprToValue e = error ("Expression cannot be converted to value:\n" ++ (show e))

myVar :: IORef a -- polymorphic ref!
myVar = unsafePerformIO $ newIORef undefined

coerce :: a -> b
coerce x = unsafePerformIO $ do
    writeIORef myVar x  -- write value of type a
    readIORef myVar     -- read value of type b

concatStmts :: Stmt -> Stmt -> Stmt
concatStmts st1 (Seq ls) = (Seq (st1 : ls))
concatStmts st1 stmt = (Seq [st1, stmt])

convertMaybe :: (Maybe Expr) -> Expr
convertMaybe (Just v) = v
convertMaybe e = error ("Error To Find Expr:\n" ++ (show e))

readMap :: String -> (M.Map String Expr) -> Expr
readMap id m = let mVal = M.lookup id m
                in convertMaybe mVal

listToInteger :: [Expr] -> [Integer]
listToInteger [] = []
listToInteger ls = let (RationalConst r) = (head ls)
                       hd = numerator r
                       tl = listToInteger (tail ls)
                    in hd : tl

exprToNumber :: Expr -> (M.Map String Expr) -> [Integer]
exprToNumber (Var id) m = let (Eset expr) = readMap id m
                              list = S.toList expr
                           in (listToInteger list)

loadCSVs :: String -> Stmt -> (M.Map String Expr) -> (IO (Stmt, (M.Map String Expr)))
loadCSVs fName (Csv identifier file columns limit tVal) m = do let csvName = addPathtoFile fName (exprToStr file)
                                                               fl <- readFile csvName 
                                                               let rows = lines fl
                                                               let cols = exprToNumber columns m
                                                               let tpy = exprToStr tVal
                                                               let exprs = createExpressions tpy 1 cols rows
                                                               let (RationalConst r) = limit
                                                               let l = numerator r
                                                               let newExprs = limitList l exprs
                                                               Prelude.return ((Assign identifier (IchoicesDist newExprs)),m)
loadCSVs fName (Assign id expr) m = do putStr ""
                                       let newM = M.insert id expr m
                                       Prelude.return ((Assign id expr),newM)
loadCSVs fName (Seq []) m = do putStr "" 
                               Prelude.return ((Seq []),m)
loadCSVs fName (Seq ls) m = do putStr ""
                               let hd = head ls
                               let tl = tail ls
                               (newHd,m1) <- (loadCSVs fName hd m)
                               (newTl,m2) <- (loadCSVs fName (Seq tl) m1)
                               Prelude.return ((concatStmts newHd newTl),m2)
loadCSVs fName (FuncStmt name body lInput) m = do putStr ""
                                                  (newBody, m1) <- (loadCSVs fName body m)
                                                  Prelude.return ((FuncStmt name newBody lInput),m1)
loadCSVs fName (Kuifje.Syntax.If e s1 s2) m = do putStr ""
                                                 (newS1,_) <- (loadCSVs fName s1 m)
                                                 (newS2,_) <- (loadCSVs fName s2 m)
                                                 Prelude.return ((Kuifje.Syntax.If e newS1 newS2),m)
loadCSVs fName (Kuifje.Syntax.While e body) m = do putStr ""
                                                   (newBody,m1) <- (loadCSVs fName body m)
                                                   Prelude.return ((Kuifje.Syntax.While e newBody),m1)
loadCSVs fName s m = do putStr ""
                        Prelude.return (s,m)

getPreffix :: String -> String
getPreffix str = let indexL = (L.findIndices (`elem` "/") str)
                    in if (L.length indexL > 0)
                       then ((fst (L.splitAt (L.last indexL) str)) ++ "/")
                       else ""

addPathtoFile :: String -> String -> String
addPathtoFile fName csvName = ((getPreffix fName) ++ csvName)

readCSVs :: String -> Stmt -> IO Stmt
readCSVs fName stmts = do stmt <- (loadCSVs fName stmts M.empty)
                          Prelude.return (fst stmt)
