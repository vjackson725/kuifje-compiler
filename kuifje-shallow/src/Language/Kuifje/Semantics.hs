{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Kuifje.Semantics where

import Data.Bifunctor (second)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Language.Kuifje.Distribution (Dist, Hyper, Prob, runD)
import qualified Language.Kuifje.Distribution as D
import Language.Kuifje.Syntax


-- | Duplicate. The 'diagonal' function.
dup :: a -> (a,a)
dup a = (a,a)


-- | Hyper-distribution type synonym.
type a ~~> b = Dist a -> Hyper b

-- | Bind with reduction applied to the input distribution.
(=>>) :: (Ord b) => Dist a -> (a -> Dist b) -> Dist b
m =>> f = D.bindDist (D.reduction m) f

-- | Kleisli composition.
(==>) :: (Ord c) => (a ~> b) -> (b ~> c) -> (a ~> c)
f ==> g = \x -> D.bindDist (f x) g

-- | For a given program, returns a function that calculates the
-- hyper-distribution for a given input distribution.
hysem :: (Ord s) => Kuifje s -> (s ~~> s)
hysem Skip          = D.returnDist
hysem (Update f p)  = huplift f ==> hysem p
hysem (If c p q r)  = conditional c (hysem p) (hysem q) ==> hysem r
hysem (While c p q) = let wh = conditional c (hysem p ==> wh) (hysem q)
                      in wh
hysem (Observe f p) = hobsem f ==> hysem p

-- | Conditional semantics ('If' and 'While').
conditional :: forall s. (Ord s) => (s ~> Bool) -> (s ~~> s) -> (s ~~> s) -> (s ~~> s)
conditional ec ct cf = \ds ->
  let h :: Map (Bool, Dist s) Prob
      h = runD . hobsemRet ec . D.reduction $ ds
      hh :: Dist (Hyper s)
      hh = D.D . M.mapKeys (\(b,d) -> if b then ct d else cf d) $ h
   in D.joinDist hh

-- | Lifts a distribution to a hyper-distribution.
huplift :: (Ord s) => (s ~> s) -> (s ~~> s)
huplift f = D.returnDist . (=>> f)

-- | 'Observe' semantics with conditioned hyperset.
--    Assumes d is reduced.
hobsemRet :: forall s o. (Ord s, Ord o) => (s ~> o) -> (Dist s ~> (o, Dist s))
hobsemRet f = \d -> gatherObs $ D.bindDist d (obsem f)
  where
    obsem :: forall a. (Ord a) => (a ~> o) -> a ~> (o, a)
    obsem f' x = D.fmapDist (,x) (f' x)

    gatherObs :: Dist (o, s) -> Dist (o, Dist s)
    gatherObs dp = D.fmapDist (second f' . dup . fst) dp
      where
        f' :: o -> Dist s
        f' ws = let dpws = D.D . M.mapKeys snd . M.filterWithKey (\(ws',_) -> const (ws == ws')) . runD $ dp
                in D.D . M.map (/ D.weight dpws) . runD $ dpws

-- | 'Observe' semantics.
hobsem :: forall s o. (Ord s, Ord o) => (s ~> o) -> (s ~~> s)
hobsem f = multiply . toPair . (=>> obsem f)
  where
    obsem :: forall a. (Ord a) => (a ~> o) -> a ~> (o, a)
    obsem f' x = D.fmapDist (,x) (f' x)

    toPair :: Dist (o, s) -> (Dist o, o -> Dist s)
    toPair dp = (d, f')
      where
        d :: Dist o
        d = D.fmapDist fst dp

        f' :: o -> Dist s
        f' ws = let dpws = D.D . M.mapKeys snd . M.filterWithKey (\(ws',_) _ -> ws == ws') . runD $ dp
                in D.D . M.map (/ D.weight dpws) . runD $ dpws

    multiply :: (Dist o, o -> Dist s) -> Hyper s
    multiply (d, f') = D.fmapDist f' d

-- | Calculate Bayes Vulnerability for a distribution.
bayesVuln :: Ord a => Dist a -> Prob
bayesVuln = (\x -> if null x then 1 else maximum x) . M.elems . runD . D.reduction

-- | Based on an entropy function for distributions, calculate the
-- average entropy for a hyper-distribution.
condEntropy :: (Dist a -> Rational) -> Hyper a -> Rational
condEntropy e m = average (D.fmapDist e m)

-- | Average a distribution of Rationals.
average :: Dist Rational -> Rational
average = sum . M.mapWithKey (*) . runD
