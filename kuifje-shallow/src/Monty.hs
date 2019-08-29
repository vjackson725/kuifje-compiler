module Monty where

import Data.List ((\\))
import Text.PrettyPrint.Boxes

import DataTypes
import PrettyPrint
import Semantics
import Syntax

data Door = DoorA | DoorB | DoorC deriving (Eq, Show, Ord)

instance ToBits Door where
  toBits DoorA = [True]
  toBits DoorB = [False,True]
  toBits DoorC = [False,False]

instance Boxable Door where
  toBox = text . show

hall :: Door -> PCL3 Door
hall chosenDoor =
  observe3 (\carDoor -> uniform ([DoorA,DoorB,DoorC] \\ [carDoor,chosenDoor]))

doors = uniform [DoorA,DoorB,DoorC]
monty = hysem (hall DoorA) doors

bv:: Ord a => Dist a -> Prob
bv = maximum . map snd . runD . reduction

condEntropy:: (Dist a -> Rational) -> Dist(Dist a) -> Rational
condEntropy e h = average (fmap e h) where
  -- | Average a distribution of Rationals.
  average:: Dist Rational -> Rational
  average d = sum [r * p | (r,p)<- runD d]

run :: IO ()
run = do
  putStrLn "> monty"
  print monty
  putStrLn "> condEntropy bv monty"
  print $ condEntropy bv monty
