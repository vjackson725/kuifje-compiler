{-# LANGUAGE GeneralizedNewtypeDeriving, TupleSections #-}
module Kuifje.TypeChecker where

import qualified Env as E
import Syntax
import Control.Applicative
import Control.Monad (void, unless)
import Data.Set
import Data.List

data Type = BoolType
          | DoubleType
          | SetOf Type
          deriving (Show, Eq, Read)

data TypeError = TypeMismatch
               | NoSuchVariable String
               | DifferentType
                deriving (Show, Eq)

type Gamma = E.Env Type

initialGamma :: Gamma
initialGamma = E.empty

newtype TC a = TC (Either TypeError a) deriving (Monad, Functor, Applicative, Show, Eq)

typeError :: TypeError -> TC a
typeError = TC . Left

typeCheck :: Gamma -> Stmt -> TC (Gamma, Stmt) 
typeCheck g (Seq []) = return (g, (Seq []))
typeCheck g (Seq ls) = 
        do (g' , e) <- typeCheck g (head ls) 
           (g'', e) <- typeCheck g' (Seq (tail ls)) 
           return (g', (Seq ls))
typeCheck g (Assign s e) 
  | Just t <- E.lookup g s = 
          case exprCheck g e of 
            (TC (Left err)) -> typeError err
            (TC (Right ty)) -> if t == ty 
                                  then return (g, (Assign s e)) 
                                  else typeError TypeMismatch
  | otherwise = 
          case exprCheck g e of 
            (TC (Left err)) -> typeError err
            (TC (Right ty)) -> let g' = E.add g (s, ty) in 
                                   return (g', (Assign s e))
typeCheck g (If e stmt1 stmt2) = 
        case exprCheck g e of 
          (TC (Left err)) -> typeError err
          (TC (Right DoubleType)) -> typeError TypeMismatch
          (TC (Right BoolType)) -> do (g1, stmt1') <- typeCheck g stmt1
                                      (g2, stmt2') <- typeCheck g stmt2
                                      return (g1, (If e stmt1 stmt2))
typeCheck g (While e stmt) = 
        case exprCheck g e of 
          (TC (Left err)) -> typeError err
          (TC (Right DoubleType)) -> typeError TypeMismatch
          (TC (Right BoolType)) -> do (g', stmt) <- typeCheck g stmt 
                                      return (g', (While e stmt))
typeCheck g Skip = return (g, Skip)
typeCheck g (Leak e) = 
        case exprCheck g e of
          (TC (Right _)) -> return (g, (Leak e))
          (TC (Left er)) -> typeError er
typeCheck g (Vis s) = return (g, (Vis s))
typeCheck g (Echoice stmt1 stmt2 e) = 
        case exprCheck g e of 
          (TC (Right BoolType))     -> typeError TypeMismatch
          (TC (Left er))            -> typeError er
          (TC (Right DoubleType)) -> 
                  do (g1, stmt1') <- typeCheck g stmt1
                     (g2, stmt2') <- typeCheck g stmt2
                     if g1 == g2 
                        then return (g1, (Echoice stmt1 stmt2 e)) 
                        else typeError TypeMismatch

exprCheck :: Gamma -> Expr -> TC Type
exprCheck g (Var s) | Just t <- E.lookup g s = return t
                    | otherwise = typeError $ NoSuchVariable s
exprCheck g (DoubleConst _) = return DoubleType
exprCheck g (Neg e) = 
        do x <- exprCheck g e 
           case x of 
             BoolType     -> return BoolType 
             DoubleType -> typeError TypeMismatch
exprCheck g (ABinary _ e1 e2) = 
        do e1' <- exprCheck g e1 
           e2' <- exprCheck g e2 
           if e1' == e2' && e1' == DoubleType 
              then return DoubleType 
              else typeError TypeMismatch
exprCheck g (Ichoice e1 e2 e3) = 
        do e1' <- exprCheck g e1 
           e2' <- exprCheck g e2 
           e3' <- exprCheck g e3
           if e1' == e2' && e3' == DoubleType
              then return e1'
              else typeError TypeMismatch
exprCheck g (Ichoices ls) = 
        do let headType = exprCheck g $ head ls
           ty <- headType
           if all (== headType) (Data.List.map (exprCheck g) $ tail ls) 
              then return ty
              else typeError TypeMismatch
exprCheck g (SetIchoice e) = 
        do e' <- exprCheck g e
           case e' of 
             (SetOf t) -> return t
             otherwise -> typeError TypeMismatch
exprCheck g (BoolConst _) = return BoolType
exprCheck g (Not e) = do e' <- exprCheck g e 
                         if e' == BoolType 
                            then return e' 
                            else typeError TypeMismatch
exprCheck g (BBinary _ e1 e2) = 
        do e1' <- exprCheck g e1 
           e2' <- exprCheck g e2 
           if e1' == e2' && e1' == BoolType
              then return BoolType
              else typeError TypeMismatch
exprCheck g (RBinary _ e1 e2) = 
        do e1' <- exprCheck g e1 
           e2' <- exprCheck g e2 
           if e1' == e2' && e1' == DoubleType
              then return BoolType
              else typeError TypeMismatch
exprCheck g (ExprIf c e1 e2) = 
        do c'  <- exprCheck g c
           e1' <- exprCheck g e1
           e2' <- exprCheck g e2
           if c' == BoolType && e1' == e2'
              then return e1'
              else typeError TypeMismatch
exprCheck g (Eset s) = 
        do let ls = Data.Set.toList s 
           let headType = exprCheck g $ head ls
           ty <- headType
           if all (== headType) (Data.List.map (exprCheck g) $ tail ls) 
              then return $ SetOf ty
              else typeError TypeMismatch
exprCheck g (Case val e1) =
        do val'  <- exprCheck val c
           e1' <- exprCheck g e1
           if val' != typeError && e1' == DoubleType
              then return e1'
              else typeError TypeMismatch
