{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Kuifje.Syntax where

import Data.Set

newtype ExprSet = Set Expr deriving (Show)

data BBinOp = And 
            | Or
            deriving (Show, Ord, Eq)
 
data SBinOp = In
            | NIn
            | IsSubOf
            deriving (Show, Ord, Eq)

data RBinOp = Gt 
            | Ge
            | Lt
            | Le
            | Eq
            | Ne
            -- Added to support Strings
            | IsSubstrOf
            deriving (Show, Ord, Eq)

data ExprTy = EBool 
            | ERational 
            deriving (Show)

data Expr = Var String 
          | RationalConst Rational
          | Neg Expr
          | Text String
          | ABinary ABinOp Expr Expr 
          | Ichoice Expr Expr Expr   -- (Expr Expr Prob)
          | IchoiceDist Expr Expr Expr   -- (Expr Expr Prob)
          | Ichoices [Expr]
          | IchoicesDist [Expr]
          | Tuple Expr Expr
          | INUchoices [Expr]
          | INUchoicesDist [Expr]
          | SetIchoice Expr
          | SetIchoiceDist Expr
          | DGaussianDist Expr Expr Expr -- mu (mean) and sigma (variance), vs
          | DLaplaceDist Expr Expr -- t (scale parameter), vs

          -- Bool Expr
          | BoolConst Bool
          | Not Expr 
          | BBinary BBinOp Expr Expr 
          | RBinary RBinOp Expr Expr
          | SBinary SBinOp Expr Expr

          -- Extension
          | TupleExpr [Expr] 
          | ExprIf Expr Expr Expr
          | Eset (Set Expr)
          | CallExpr String [Expr]
          | ListExpr [Expr]
          | ListElem String Expr
          | ListAppend String Expr
          | ListInsert String Expr Expr
          | ListExtend String String
          | ListRemove String Expr
          | ListLength Expr
          | ListElemDirect [Expr] Expr
          | Geometric Expr Expr Expr Expr
          | PowerSet Expr
          deriving (Show, Eq, Ord)

data ABinOp = Add 
            | Subtract 
            | Multiply 
            | Divide 
            | Pow
            | IDivide 
            | Rem
            | Intersection
            | Filter
            deriving (Show, Ord, Eq)

data Stmt = Seq [Stmt]
          | Assign String Expr
          | Plusplus String
          | Lessless String
          | Sampling String Expr
          | If Expr Stmt Stmt
          | While Expr Stmt
          | For String Expr Stmt
          | FuncStmt String Stmt [String] --[Expr]
          | ReturnStmt Expr
          | Support String Expr
          | Csv String Expr Expr Expr Expr
          | Skip 
          | Leak Expr
          | Vis String
          | Echoice Stmt Stmt Expr
deriving instance Show Stmt
