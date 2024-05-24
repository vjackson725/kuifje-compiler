{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Kuifje.Env ( Env(..)
                 , empty
                 , singleton
                 , lookup
                 , add
                 , addAll
                 , allVar
                 , envFromList
                 , restrictVars
                 , withoutVars
                 ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Monoid
import Prelude hiding (lookup)

newtype Env e = Env (M.Map String e) 
    deriving (Functor, Foldable, Traversable, Show, Eq, Ord)

empty :: Env e
empty = Env M.empty

singleton :: String -> e -> Env e
singleton x e = Env (M.singleton x e)

lookup :: Env e -> String -> Maybe e
lookup (Env env) var = M.lookup var env

add :: Env e -> (String, e) -> Env e
add (Env env) (key,elt) = Env (M.insert key elt env)

addAll :: Env e -> [(String,e)] -> Env e
addAll (Env env) pairs = Env $ foldr (\(k,e) g -> M.insert k e g) env pairs

unpackM :: Env e -> (M.Map String e) 
unpackM (Env env) = env

allVar :: Env e -> [String]
allVar (Env env) = [ s | (s, _) <- M.toList env]

envFromList :: [(String,e)] -> Env e
envFromList xs = Env (M.fromList xs)

restrictVars :: S.Set String -> Env e -> Env e
restrictVars ks (Env m) = Env $ M.restrictKeys m ks

withoutVars :: S.Set String -> Env e -> Env e
withoutVars ks (Env m) = Env $ M.withoutKeys m ks
