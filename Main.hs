module Main where

import Control.Applicative (empty)
import Control.Monad (when)

import System.Environment
import Kuifje.Run

main =
  do
    args <- getArgs
    if null args
    then putStrLn "provide a file"
    else 
      let file = head args
          flags = tail args
       in runFileDefaultParams file flags
--           in do runHyper file flags
--          case args of
--            [file]    -> do runHyper file
--            otherwise -> error "Please provide a file."
