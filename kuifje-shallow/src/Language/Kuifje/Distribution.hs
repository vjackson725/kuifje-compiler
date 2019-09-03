{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Kuifje.Distribution where

import Prelude hiding (filter, foldr, return)
import Data.List (genericLength)
import Data.Map.Strict

-- | Type synonym for probabilities.
type Prob = Rational

-- | Distribution data type.
newtype Dist a = D { runD :: Map a Prob }

-- instance Hashable a => Hashable (Dist a) where
--   hashWithSalt salt (D s) = hashWithSalt salt s

fmap :: (Ord b) => (a -> b) -> Dist a -> Dist b
fmap f dx = dx `bind` (return . f)

return :: (Ord a) => a -> Dist a
return x = D $ singleton x 1

bind :: (Ord b) => Dist a -> (a -> Dist b) -> Dist b
d `bind` f = D $ fromListWith (+) [(y, p * q) | (x, p) <- toList $ runD d, (y, q) <- toList $ runD (f x)]

join :: (Ord a) => Dist (Dist a) -> Dist a
join x = x `bind` id

instance Ord a => Eq (Dist a) where
  d1 == d2  =  unpackD d1 == unpackD d2

instance Ord a => Ord (Dist a) where
  d1 <= d2  =  unpackD d1 <= unpackD d2

-- | Construct a discrete distribution from a nonempty list of elements,
-- assigning the same probability to each element.
uniform :: (Ord a) => [a] -> Dist a
uniform l = D $ fromListWith (+) [(x, 1 / genericLength l) | x <- l]

-- | Construct a distribution in which the first element has probability p
-- and the second 1−p.
choose :: (Ord a) => Prob -> a -> a -> Dist a
choose p x y = D $ fromListWith (+) [(x, p), (y, 1 - p)]

-- | Recover the list representation of a distribution, reduced.
unpackD :: Dist a -> Map a Prob
unpackD = removeZeroes . runD -- TODO: integrate to reduction
  where
    removeZeroes = filter (\(p) -> p /= 0)

-- | Remove duplicates and zeroes from a distribution.
reduction :: Dist a -> Dist a
reduction = D . unpackD

-- | Sum the probabilities in the distribution.
weight :: Dist a -> Prob
weight (D l) = foldr (+) 0 l
