{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Kuifje.Semantics where

import qualified Data.Map.Strict as M

import Language.Kuifje.Distribution
import Language.Kuifje.Syntax

-- | Hyper-distribution type synonym.
type a ~~> b = Dist a -> Hyper b

-- | Bind with reduction applied to the input distribution.
(=>>) :: (Ord b) => Dist a -> (a -> Dist b) -> Dist b
m =>> f = bindDist (reduction m) f

-- | Kleisli composition.
(==>) :: (Ord c) => (a ~> b) -> (b ~> c) -> (a ~> c)
f ==> g = \x -> bindDist (f x) g

-- | For a given program, returns a function that calculates the
-- hyper-distribution for a given input distribution.
hysem :: (Ord s) => Kuifje s -> (s ~~> s)
hysem Skip          = returnDist
hysem (Update f p)  = huplift f ==> hysem p
hysem (If c p q r)  = conditional c (hysem p) (hysem q) ==> hysem r
hysem (While c p q) = let wh = conditional c (hysem p ==> wh) (hysem q)
                      in wh
hysem (Observe f p) = hobsem f ==> hysem p

-- | Conditional semantics ('If' and 'While').
conditional :: forall s. (Ord s) => (s ~> Bool) -> (s ~~> s) -> (s ~~> s) -> (s ~~> s)
conditional ec pt pf = \d ->
  let d' :: Dist (Bool, s)
      d' = probListToDist $ do
                              s <- distToProbList . reduction $ d
                              b <- distToProbList . reduction . ec $ s
                              return (b, s)
      w1 = weight . probListToDist . filterProbList fst . distToProbList $ d'
      w2 = 1 - w1
      d1 = D $ M.fromListWith (+) [(s, p / w1) | ((b, s), p) <- M.toList $ runD d', b]
      d2 = D $ M.fromListWith (+) [(s, p / w2) | ((b, s), p) <- M.toList $ runD d', not b]
      h1 = pt d1
      h2 = pf d2
   in if      null (runD d2) then h1
      else if null (runD d1) then h2
                             else joinDist (choose w1 h1 h2)

-- | Lifts a distribution to a hyper-distribution.
huplift :: (Ord s) => (s ~> s) -> (s ~~> s)
huplift f = returnDist . (=>> f)

-- | 'Observe' semantics.
hobsem :: forall s o. (Ord s, Ord o) => (s ~> o) -> (s ~~> s)
hobsem f = multiply . toPair . (=>> obsem f)
  where
    obsem :: forall a. (Ord a) => (a ~> o) -> a ~> (o, a)
    obsem f' x = fmapDist (,x) (f' x)

    toPair :: Dist (o, s) -> (Dist o, o -> Dist s)
    toPair dp = (d, f')
      where
        d :: Dist o
        d = fmapDist fst dp

        f' :: o -> Dist s
        f' ws = let dpws = D . M.mapKeys snd . M.filterWithKey (\(ws',_) _ -> ws == ws') . runD $ dp
                in D . M.map (/ weight dpws) . runD $ dpws

    multiply :: (Dist o, o -> Dist s) -> Hyper s
    multiply (d, f') = fmapDist f' d

-- | Calculate Bayes Vulnerability for a distribution.
bayesVuln :: Ord a => Dist a -> Prob
bayesVuln = maximum . M.elems . runD . reduction

-- | Based on an entropy function for distributions, calculate the
-- average entropy for a hyper-distribution.
condEntropy :: (Dist a -> Rational) -> Hyper a -> Rational
condEntropy e m = average (fmapDist e m)

-- | Average a distribution of Rationals.
average :: Dist Rational -> Rational
average = sum . M.mapWithKey (*) . runD
