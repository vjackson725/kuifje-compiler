{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.CsvLoader where

import System.Environment
import System.IO
import System.IO.Unsafe
import Data.IORef
import Data.Ratio

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

selectCols :: Integer -> [Integer] -> [String] -> [Expr]
selectCols _ [] [] = []
selectCols id cols val = let hdCols = head cols
                          in if id == hdCols
                             then let hdVal = head val
                                      tlCols = tail cols
                                      tlVal = tail val
                                      tl = selectCols (id+1) tlCols tlVal
                                   in ((Text hdVal) : tl)
                             else (selectCols (id+1) cols (tail val))

createExpressions :: [Integer] -> [String] -> [Expr]
createExpressions _ [] = []
createExpressions cols ls = let hd = head ls
                                tl = createExpressions cols (tail ls)
                                cl = wordsWhen (==',') hd
                                vals = selectCols 0 cols cl
                                set = S.fromList vals
                             in (Eset set) : tl --error ("vals is:\n" ++ (show vals))--(Eset set) : tl

exprToStr :: Expr -> String
exprToStr (Text t) = t
exprToStr e = error ("Invalid Filename:\n  " ++ (show e))

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
loadCSVs fName (Csv identifier file columns) m = do let csvName = addPathtoFile fName (exprToStr file)
                                                    fl <- readFile csvName 
                                                    let rows = lines fl
                                                    let cols = exprToNumber columns m
                                                    let exprs = createExpressions cols rows
                                                    let values = S.fromList exprs
                                                    let expr = (SetIchoiceDist (Eset values))
                                                    Prelude.return ((Assign identifier expr),m)
                                                    --error ("exprS is:\n" ++ (show expr))
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

--parseCSVs :: [Expr] -> IO Stmt
--parseCSVs file =
--        do program  <- readFile file
--           case parse statements "" program of
--                Left e  -> print e >> fail "parse error"
--                Right r -> return r

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
                       --do let csvName = addPathtoFile fName "100020.csv"
                       --   file <- readFile csvName --"100020.csv" ReadMode
                       --   error ("Content is:\n" ++ file)
 --error ("Called to" ++ (show stmts))

--createJson2 :: String -> [(String, (Dist (Dist Value)))] -> IO ()
--createJson2 fName values = do let s = 4
--                              let jContent = "{\n" ++ (variableJson2 s values) ++ "\n}"
--                              let jName = jsonName2 fName
--                              jsonFile <- openFile jName WriteMode
--                              hPutStrLn jsonFile jContent
--                              hClose jsonFile
