{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Language.Kuifje.Syntax where

import Language.Kuifje.Distribution

-- | Kleisli arrow.
type a ~> b = a -> Dist b

-- | Syntax of the Kuifje language.
data Kuifje s where
  Skip :: Kuifje s
  Update :: (s ~> s) -> Kuifje s -> Kuifje s
  If :: (s ~> Bool) -> Kuifje s -> Kuifje s -> Kuifje s -> Kuifje s
  While :: (s ~> Bool) -> Kuifje s -> Kuifje s -> Kuifje s
  Observe :: Ord o => (s ~> o) -> Kuifje s -> Kuifje s

instance Show s => Show (Kuifje s) where
  show Skip = "Skip"
  show (Update _ k) = "Update <fun>; " ++ show k
  show (If _ astt astf k) = "If <test> (" ++ show astt ++ ") (" ++ show astf ++ ") Fi; " ++ show k
  show (While _ ast k) = "While <test> (" ++ show ast ++ ") Done; " ++ show k
  show (Observe _ k) = "Observe <fun>; " ++ show k

instance Semigroup (Kuifje s) where
  Skip        <> k = k
  Update f p  <> k = Update f (p <> k)
  While c p q <> k = While c p (q <> k)
  If c p q r  <> k = If c p q (r <> k)
  Observe f p <> k = Observe f (p <> k)

instance Monoid (Kuifje s) where
  mempty = Skip
  mappend = (<>)

-- | Return a 'Skip' instruction.
skip :: Kuifje s
skip = Skip

-- | Return an 'Update' instruction.
update :: (s ~> s) -> Kuifje s
update f = Update f skip

-- | Return a 'While' instruction.
while :: (s ~> Bool) -> Kuifje s -> Kuifje s
while c p = While c p skip

-- | Return an 'If' instruction.
cond :: (s ~> Bool) -> Kuifje s -> Kuifje s -> Kuifje s
cond c p q = If c p q skip

-- | Return an 'Observe' instruction.
observe :: (Ord o) => (s ~> o) -> Kuifje s
observe o = Observe o skip
