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

data RBinOp = Gt 
            | Ge
            | Lt
            | Le
            | Eq
            | Ne
            deriving (Show, Ord, Eq)

data ExprTy = EBool 
            | ERational 
            deriving (Show)

data Expr = Var String 
          | RationalConst Rational
          | Neg Expr 
          | ABinary ABinOp Expr Expr 
          | Ichoice Expr Expr Expr   -- (Expr Expr Prob)
          | Ichoices [Expr]
          | Tuple Expr Expr
          | INUchoices [Expr]
          | SetIchoice Expr

          -- Bool Expr
          | BoolConst Bool
          | Not Expr 
          | BBinary BBinOp Expr Expr 
          | RBinary RBinOp Expr Expr 

          -- Extension
          | ExprIf Expr Expr Expr
          | Eset (Set Expr)
          | Case Expr Expr
          | ExprSwitch Expr [Expr] Expr
          | Geometric Expr Expr Expr Expr
          deriving (Show, Eq, Ord)

data ABinOp = Add 
            | Subtract 
            | Multiply 
            | Divide 
            | Pow
            | IDivide 
            | Rem
            deriving (Show, Ord, Eq)

data Stmt = Seq [Stmt]
          | Assign String Expr
          | If Expr Stmt Stmt
          | While Expr Stmt
          | FuncStmt String Stmt [String] --[Expr]
          | ReturnStmt [Expr]
          | CallStmt String [Expr] [String]
          | Switch Expr [Stmt] Stmt
          | CaseStmt Expr Stmt
          | Skip 
          | Leak Expr
          | Vis String
          | Echoice Stmt Stmt Expr
deriving instance Show Stmt
