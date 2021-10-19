module Kuifje.Run where

import Kuifje.Translator
import Kuifje.Parse
import Kuifje.Value
import Kuifje.Syntax
import Kuifje.PrettyPrint 
import System.IO 
import Data.Map.Strict
import Data.List
import Language.Kuifje.Distribution
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Prelude hiding ((!!), fmap, (>>=))
import qualified Kuifje.Env as E
import qualified Data.Map as Map

getFrom g s | Just x <- E.lookup g s = x
            | otherwise = error ("Not going to happend " ++ s)
            
project :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
project var = fmap (fmap (\s -> getFrom s var))

runHyper s = do tmp <- parseFile s
                let m = Map.empty
                let g = fst (translateKuifje tmp m)
                let kuifje = hysem g (uniform [E.empty])
                let (env, _) = (toList $ runD kuifje) !! 0
                let (gamma, _) = ((toList $ runD $ env) !! 0)
                let all_var = E.allVar gamma
                --error ("\nVars are:\n" ++ (show all_var) ++ "\n")
                outputL [(x, Kuifje.Run.project x kuifje) | x <- all_var]


outputL (ls) = if length ls == 1 
                  then do putStrLn $ "> Variable " ++ (fst $ head ls) ++ " hyper"
                          print $ snd $ head ls
                          putStrLn "> condEntropy bayesVuln hyper"
                          putStrLn ""
                          print $ condEntropy bayesVuln $ snd $ head ls
                  else do putStrLn $ "> Variable " ++ (fst $ head ls) ++ " hyper"
                          print $ snd $ head ls
                          putStrLn "> condEntropy bayesVuln hyper"
                          print $ condEntropy bayesVuln $ snd $ head ls
                          putStrLn ""
                          outputL $ tail ls

runFile :: String -> IO ()
runFile s = do runHyper s
