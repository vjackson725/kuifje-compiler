module Main where

import Control.Applicative (empty)
import Control.Monad (when)
import Data.List (isPrefixOf)

import System.Environment
import Kuifje.Run

main :: IO ()
main =
  do
    args <- getArgs
    case args of
      [] ->
        putStrLn "please provide a file"
      (mode : file : flags) | not . isPrefixOf "-" $ file ->
        case mode of
          "run" -> runFileDefaultParams file flags
          "ldists" | (invar:svals:_) <- flags ->
                      leakDists file invar svals
                   | otherwise ->
                      putStrLn "ldists requires an input var and a list of input values"
          _ -> putStrLn "provided an unknown compiler mode"
      (file : flags) ->
        runFileDefaultParams file flags
