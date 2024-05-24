{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Kuifje.Distribution where

import qualified Data.Map.Strict as M
import Data.Bifunctor (first)
import Data.List (genericLength)
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe)

-- | Type synonym for probabilities.
type Prob = Rational


-- | List of values with probabilities.
--   Probabilities should be in (0,1].
--   Values may be duplicated.
newtype ProbList a = ProbList { unProbList :: [(a,Prob)] }
  deriving (Show)

-- if f is not injective, values can become duplicated
instance Functor ProbList where
  fmap f = ProbList . fmap (first f) . unProbList

instance Applicative ProbList where
  pure x = ProbList [(x,1)]
  fs <*> xs = ProbList [ (f x, p*q) | (x,q) <- unProbList xs, (f,p) <- unProbList fs ]

instance Monad ProbList where
  xs >>= f =
    ProbList $
      (do
        (x,p) <- unProbList xs
        (y,q) <- unProbList $ f x
        return (y, p * q))

instance Foldable ProbList where
  foldr :: (a -> b -> b) -> b -> ProbList a -> b
  foldr f b (ProbList xs) = foldr (f . fst) b xs

filterProbList :: (a -> Bool) -> ProbList a -> ProbList a
filterProbList p (ProbList xs) = ProbList (filter (p . fst) xs)


-- | Distribution data type.
newtype Dist a = D { runD :: Map a Prob }
  deriving (Show)

-- | Recover the map representation of a distribution, reduced.
unpackD :: Dist a -> Map a Prob
unpackD = M.filter (/= 0) . runD

-- | Remove zeroes from a distribution.
reduction :: Dist a -> Dist a
reduction = D . unpackD

instance Ord a => Eq (Dist a) where
  d1 == d2  =  unpackD d1 == unpackD d2

instance Ord a => Ord (Dist a) where
  d1 <= d2  =  unpackD d1 <= unpackD d2


-- | Type alias for hyper-distributions.
type Hyper a = Dist (Dist a)


-- | Convert from Dist to [(a, Prob)]
distToList :: Dist a -> [(a, Prob)]
distToList = M.toList . runD

-- | Convert from [(a, Prob)] to Dist
listToDist :: Ord a => [(a, Prob)] -> Dist a
listToDist = D . M.fromListWith (+)

-- | Convert from Dist to ProbList
distToProbList :: Dist a -> ProbList a
distToProbList = ProbList . M.toList . runD

-- | Convert from ProbList to Dist
probListToDist :: Ord a => ProbList a -> Dist a
probListToDist = D . M.fromListWith (+) . unProbList


-- | normalises a distribution
normalise :: Dist a -> Dist a
normalise (D m) =
  let sum = M.foldr (+) 0 m
  in D $ M.map (/ sum) m


-- | fmap function for distributions.
fmapDist :: (Ord b) => (a -> b) -> Dist a -> Dist b
fmapDist f = probListToDist . fmap f . distToProbList

-- | condition the Dist on a predicate
filterDist :: (Ord a) => (a -> Bool) -> Dist a -> Dist a
filterDist p = listToDist . filter (p . fst) .  distToList

-- | mapMaybe function for distributions.
--   !NOTE! does not renormalise the distribution!
mapMaybeDist :: (Ord b) => (a -> Maybe b) -> Dist a -> Dist b
mapMaybeDist f = listToDist . mapMaybe (\(a,p) -> (,p) <$> f a) . distToList

-- | Renomalising mapMaybe function for distributions.
conditionMaybeDist :: (Ord b) => (a -> Maybe b) -> Dist a -> Dist b
conditionMaybeDist f = normalise . listToDist . mapMaybe (\(a,p) -> (,p) <$> f a) . distToList

-- | fmap function for distributions, where f is injective.
--   Requires f is injective on all values in the domain of the Dist.
fmapDistInj :: (Ord b) => (a -> b) -> Dist a -> Dist b
fmapDistInj f = D . M.fromList . unProbList . fmap f . distToProbList

-- | Top-level return function for distributions. Creates a singleton
-- distribution.
returnDist :: (Ord a) => a -> Dist a
returnDist x = D $ M.singleton x 1

-- | Alias for return function.
point :: Ord a => a -> Dist a
point = returnDist

-- | Top-level bind function for distributions.
bindDist :: (Ord b) => Dist a -> (a -> Dist b) -> Dist b
bindDist d f = probListToDist $ (>>=) (distToProbList d) (distToProbList . f)

-- | Top-level join function for distributions.
joinDist :: (Ord a) => Dist (Dist a) -> Dist a
joinDist x = bindDist x id

-- | fmap function for distributions.
sequenceDist :: (Traversable t, Ord (t a)) => t (Dist a) -> Dist (t a)
sequenceDist = probListToDist . sequenceA . fmap distToProbList

-- | fmap function for distributions.
traverseDist :: (Traversable t, Ord (t b)) => (a -> Dist b) -> t a -> Dist (t b)
traverseDist f = probListToDist . traverse (distToProbList . f)


-- | Construct a discrete distribution from a nonempty list of elements,
-- assigning the same probability to each element.
uniform :: (Ord a) => [a] -> Dist a
uniform l = D $ M.fromListWith (+) [(x, 1 / genericLength l) | x <- l]

-- | Construct a distribution in which the first element has probability p
-- and the second 1−p.
choose :: (Ord a) => Prob -> a -> a -> Dist a
choose p x y = D $ M.fromListWith (+) [(x, p), (y, 1 - p)]

-- | Sum the probabilities in the distribution.
weight :: Dist a -> Prob
weight = M.foldr (+) 0 . runD

-- | The bernoulli distribution between a and b, with weight w.
bernoulli :: Ord a => a -> a -> Prob -> Dist a
bernoulli a b w = D $ M.fromList [(a, w),(b, 1-w)]


-- | The bernoulli distribution between a and b, with weight w.
null :: Dist a -> Bool
null = M.null . runD