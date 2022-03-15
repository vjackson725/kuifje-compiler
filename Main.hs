module Main where

import System.Environment
import Kuifje.Run

main = do args <- getArgs
          let file = head args
              flags = tail args
           in  runFileDefaultParams file flags
--           in do runHyper file flags
--          case args of
--            [file]    -> do runHyper file
--            otherwise -> error "Please provide a file."
