module Kuifje.Run where

import Kuifje.Translator
import Kuifje.Parse
import Kuifje.Value
import Kuifje.Syntax
import Kuifje.PrettyPrint 
import qualified Kuifje.Env as E

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

runHyper s = do tmp <- parseFile s
                let m = Map.empty
                let e = Map.empty
                --let g = fst3 (translateKuifje tmp m e)
                let l = fst3 (translateExecKuifje tmp m e [])
                let g = createMonnad l 
                let kuifje = hysem g (uniform [E.empty])
                let (env, _) = (toList $ runD kuifje) !! 0
                let (gamma, _) = ((toList $ runD $ env) !! 0)
                let all_var = E.allVar gamma
                --error ("\nVars are:\n" ++ (show all_var) ++ "\n")
                outputL [(x, Kuifje.Run.project x kuifje) | x <- all_var]



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

runFile :: String -> IO ()
runFile s = do runHyper s
