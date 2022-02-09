{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.CsvLoader where

import System.Environment
import System.IO
import System.IO.Unsafe
import Data.IORef

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

isComma :: Char -> Bool
isComma c = (c == ',')

divideCols :: String -> [String]
divideCols s = case dropWhile {-partain:Char.-}isComma s of
               "" -> []
               s' -> w : words s''
                     where (w, s'') =
                            break {-partain:Char.-}isComma s'

createExpressions :: [String] -> [Expr]
createExpressions [] = []
createExpressions ls = let hd = head ls
                           tl = tail ls
                           list = createExpressions tl
                           cl = divideCols hd
                        in error ("Col: " ++ (show cl))


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

loadCSVs :: String -> Stmt -> IO Stmt
loadCSVs fName (Csv identifier file columns) = do let csvName = addPathtoFile fName (exprToStr file)
                                                  fl <- readFile csvName 
                                                  let rows = lines fl
                                                  let exprs = createExpressions rows
                                                  error ("Stub")
loadCSVs fName (Seq []) = (Seq [])
loadCSVs fName (Seq ls) = do let hd = head ls
                             let tl = tail ls
                             newHd <- loadCSVs fName hd
                             newTl <- loadCSVs fName (Seq tl)
                             concatStmts newHd newTl
loadCSVs fName (FuncStmt name body lInput) = do newBody <- loadCSVs fName body
                                                (FuncStmt name newBody lInput)
loadCSVs fName (Kuifje.Syntax.If e s1 s2) = do newS1 <- loadCSVs fName s1
                                               newS2 <- loadCSVs fName s2
                                               (Kuifje.Syntax.If e newS1 newS2)
loadCSVs fName (Kuifje.Syntax.While e body) = do newBody <- loadCSVs fName body
                                                 (Kuifje.Syntax.While e newBody)
loadCSVs fName s = s

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
readCSVs fName stmts = loadCSVs fName stmts
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
