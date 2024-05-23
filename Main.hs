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
          "etable" | (invar:outvar:svals:_) <- flags ->
                      uniformEpsilonTable file invar outvar svals
                   | otherwise ->
                      putStrLn "etable requires an input var, an output var, and a list of inputs"
          _ -> putStrLn "provided an unknown compiler mode"
      (file : flags) ->
        runFileDefaultParams file flags
