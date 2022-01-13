module Kuifje.Run where

import Kuifje.Translator
import Kuifje.Parse
import Kuifje.Value
import Kuifje.Syntax
import Kuifje.PrettyPrint 
import Kuifje.JsonPrint
import qualified Kuifje.Env as E

import System.Environment

import System.IO 
import Data.Map.Strict
import Data.List
import Language.Kuifje.Distribution
import Language.Kuifje.PrettyPrint
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Text.PrettyPrint.Boxes (printBox)
import Prelude hiding ((!!), fmap, (>>=))
import qualified Data.Map as Map

getFrom g s | Just x <- E.lookup g s = x
            | otherwise = error ("Not going to happend " ++ s)
            
project :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
project var = fmap (fmap (\s -> getFrom s var))

processFlag :: String -> String -> [(String, (Dist (Dist Value)))] -> IO ()
processFlag "json1" fName values = createJson1 fName values
processFlag f _ _ = error ("\n\n  Unknown flag:\n" ++ f ++ "\n")

readFlags :: [String] -> String -> [(String, (Dist (Dist Value)))] -> IO ()
readFlags [] fName _ = putStrLn $ ""
readFlags ls fName variables = do processFlag (head ls) fName variables
                                  readFlags (tail ls) fName variables

runHyper s ls = do tmp <- parseFile s
                   let m = Map.empty
                   let e = Map.empty
                   let l = fst3 (translateExecKuifje tmp m e (L []))
                   let v = runLivenessAnalysis l
                   let g = createMonnad l 
                   let kuifje = hysem g (uniform [E.empty])
                   let (env, _) = (toList $ runD kuifje) !! 0
                   let (gamma, _) = ((toList $ runD $ env) !! 0)
                   let all_var = E.allVar gamma
                   if v then
                      do let output = [(x, Kuifje.Run.project x kuifje) | x <- all_var]
                         readFlags ls s output
                         outputL output 
                        --outputL [(x, Kuifje.Run.project x kuifje) | x <- all_var]
                   else error ("\n\nCompilation fatal error.\n\n")

outputL :: (Ord a, Boxable a) => [(String, Hyper a)] -> IO ()
outputL ls =
  mapM_ (\l ->
    do
      putStrLn $ "> Variable " ++ fst l ++ " hyper"
      printBox . toBox . snd $ l
      putStrLn $ "> condEntropy bayesVuln " ++ fst l ++ " hyper"
      printBox . toBox . condEntropy bayesVuln . snd $ l
      putStrLn ""
  ) ls

runFile :: String -> [String] -> IO ()
runFile s ls = runHyper s ls
