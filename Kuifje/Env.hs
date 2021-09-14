{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}

module Kuifje.Env ( Env(..)
                 , empty
                 , lookup
                 , add
                 , addAll
                 , allVar
                 , allCntx
                 ) where

import qualified Data.Map as M
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid
import Prelude hiding (lookup)

newtype Env e = Env (M.Map (String, String) e) 
        deriving (Functor, Foldable, Traversable, Show, Eq, Ord)

empty :: Env e
empty = Env M.empty

lookup :: Env e -> (String, String) -> Maybe e
lookup (Env env) (scope,name) = M.lookup (scope,name) env

add :: Env e -> (String, String, e) -> Env e
add (Env env) (scope,name,elt) = Env (M.insert (scope,name) elt env)

addAll :: Env e -> [(String,String,e)] -> Env e
addAll (Env env) pairs = Env $ foldr (\(s,n,e) g -> M.insert (s,n) e g) env pairs

allVar :: Env e -> [String]
allVar (Env env) = [ b | ((_, b), _) <- M.toList env]

allCntx :: Env e -> [String]
allCntx (Env env) = [ a | ((a, _), _) <- M.toList env]

