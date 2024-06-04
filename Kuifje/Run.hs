module Kuifje.Run where

import Debug.Trace (traceShowId)

import Kuifje.Stmt
import Kuifje.Translator (translateExecKuifje, fst3)
import Kuifje.LivenessAnalysis
import Kuifje.Parse
import Kuifje.Value
import Kuifje.Syntax
import Kuifje.PrettyPrint 
import Kuifje.JsonPrint
import Kuifje.CsvLoader
import Kuifje.Env (Env)
import qualified Kuifje.Env as E

import Control.Monad (when)
import Data.Bifunctor
import Data.IORef
import Data.List
import Data.Ratio ((%))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as S
import System.Environment
import System.IO
import qualified Text.PrettyPrint.Boxes as PP
import Text.Printf (printf)

import Language.Kuifje.Distribution (Hyper, Dist, fmapDist, traverseDist)
import qualified Language.Kuifje.Distribution as D
import Language.Kuifje.PrettyPrint
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Language.Kuifje.ShallowConsts

project :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
project var = fmapDist (D.mapMaybeDist (flip E.lookup var))

-- | restrict every env in the hyper to contain only the variables in `vars`
projectVars :: S.Set String -> Dist (Dist Gamma) -> Dist (Dist Gamma)
projectVars vars = fmapDist (D.fmapDist (E.restrictVars vars))

-- | restrict every env in the hyper to contain only the variables not in `vars`
projectVarsCompl :: S.Set String -> Dist (Dist Gamma) -> Dist (Dist Gamma)
projectVarsCompl vars = fmapDist (D.fmapDist (E.withoutVars vars))

processFlag :: String -> String -> [(String, (Dist (Dist Value)))] -> IO ()
processFlag "json1" fName values = createJson1 fName values
processFlag "json2" fName values = createJson2 fName values
processFlag f _ _ = error ("\n\n  Unknown flag:\n" ++ f ++ "\n")

readFlags :: [String] -> String -> [(String, Dist (Dist Value))] -> IO ()
readFlags [] fName _ = putStrLn $ ""
readFlags ls fName variables = do processFlag (head ls) fName variables
                                  readFlags (tail ls) fName variables

--runHyper :: String -> [String] -> IO ()
--runHyper s ls = do tmp <- parseFile s
--                   let m = Map.empty
--                   let e = Map.empty
--                   st <- readCSVs s tmp
--                   let l = fst3 (translateExecKuifje st m e (L []))
--                   let v = runLivenessAnalysis l
--                   let g = createMonnad l 
--                   let kuifje = hysem g (uniform [E.empty])
--                   let (env, _) = (toList $ runD kuifje) !! 0
--                   let (gamma, _) = ((toList $ runD $ env) !! 0)
--                   let all_var = E.allVar gamma
--                   writeDecimalPrecision 6
--                   if v then
--                      do let output = [(x, Kuifje.Run.project x kuifje) | x <- all_var]
--                         readFlags ls s output
--                         outputL output 
--                   else error ("\n\nCompilation fatal error.\n\n")

outputL :: (Ord a, Boxable a) => [(String, Hyper a)] -> IO ()
outputL ls =
  mapM_ (\l ->
    do
      putStrLn $ "> Variable " ++ fst l ++ " hyper"
      PP.printBox . toBox . snd $ l
      putStrLn $ "> condEntropy bayesVuln " ++ fst l ++ " hyper"
      PP.printBox . toBox . condEntropy (D.probToRational . bayesVuln) . snd $ l
      putStrLn ""
  ) ls

compileFile filename =
  do
    file <- parseFile filename
    let map1 = Map.empty
    let map2 = Map.empty
    st <- readCSVs filename file
    let ast =  fst3 (translateExecKuifje st map1 map2 (L []))
    return ast

runFile :: String -> Dist Gamma -> IO (Hyper Gamma)
runFile filename distrib =
  do
    ast <- compileFile filename
    let v = runLivenessAnalysis ast
    let monadAst = createMonnad ast
    if v then
      return (hysem monadAst distrib)
    else error ("\n\nCompilation fatal error.\n\n")

runFileDefaultParams :: String -> [String] -> IO ()
runFileDefaultParams s param =
  do
    hyper <- runFile s (D.uniform [E.empty])
    let getVars :: Hyper Gamma -> [String]
        getVars = M.foldMapWithKey (\k _ -> M.foldMapWithKey (\k _ -> E.allVar k) . D.runD $ k) . D.runD
        allvars :: [String]
        allvars = nub . sort . getVars $ hyper
    let output = [(x, project x hyper) | x <- allvars]
    when (null output) (fail "no variables in output hyper")
    readFlags param s output
    writeDecimalPrecision 6
    outputL output

leakDists :: String -> String -> String -> IO ()
leakDists file invar svals =
  do
    let vals :: [Rational]
        vals =  map ((% 1) . toInteger) $ read svals
    hyper <- runFile file $ D.point E.empty
    let -- | condition the inners by the values `vals` that `invar` takes
        conditioned :: [(Rational, Dist (Dist Gamma))]
        conditioned = map (\x -> (x, condition x hyper)) vals
          where
            condPred :: Rational -> Gamma -> Maybe Gamma
            condPred x env =
              case E.lookup env invar of
                Just x' | x' == R x -> Just $ E.withoutVars (S.fromList [invar]) env
                otherwise -> Nothing
            condition :: Rational -> Hyper Gamma -> Hyper Gamma
            condition x =
              D.conditionMaybeDist (\d -> if D.null d then Nothing else Just d)
              . D.fmapDist (D.conditionMaybeDist (condPred x)) 
    writeDecimalPrecision 6 -- set the decimal precision to output
    putStrLn "Conditioned hypers:"
    mapM_
      (\(x, h) ->
        do
          putStrLn (invar ++ " == " ++ show x)
          PP.printBox . ((PP.<+>) (PP.text "  ")) . toBox $ h
          putStrLn ""
      )
      conditioned

