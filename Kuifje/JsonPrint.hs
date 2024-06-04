{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.JsonPrint where

import System.Environment
import System.IO

import Kuifje.Value

import Text.PrettyPrint.Boxes
import qualified Data.Set as S
import qualified Data.Map as M
import Numeric
--import Language.Kuifje.PrettyPrint
import Language.Kuifje.Distribution

import Kuifje.Env

-------------------------------------------------------------------------------
--                         General Functions
-------------------------------------------------------------------------------

-- Generates an organized code
spaceGen :: Integer -> String
spaceGen 0 = ""
spaceGen n = " " ++ (spaceGen (n-1))

variableLabel :: Integer -> String -> String -> String
variableLabel s name content = let v1 = (spaceGen s) ++ "\"" ++ name ++ "\" : {\n"
                                   v2 = v1 ++ content ++ "\n" ++ (spaceGen s) ++ "}"
                                in v2

boolToString :: Bool -> String
boolToString True = "TRUE"
boolToString False = "FALSE"

recoverSetElements :: [Value] -> String
recoverSetElements [] = ""
recoverSetElements ls = let hd = recoverValues (head ls)
                            tl = recoverSetElements (tail ls)
                         in if tl /= "" then
                               hd ++ ", " ++ tl
                            else hd

recoverValues :: Value -> String
recoverValues (R x) = "R " ++ (show (fromRat x))
recoverValues (T x) = "T " ++ x
recoverValues (B x) = "B " ++ (boolToString x)
recoverValues (S x) = let list = S.elems x
                       in "S [" ++ recoverSetElements list ++ "]"

-------------------------------------------------------------------------------
--                  Dencriptive JSON format supported
-------------------------------------------------------------------------------

-- Unpacking values
recoverD2FromList :: Integer -> [(Value, Prob)] -> String
recoverD2FromList s [] = ""
recoverD2FromList s ls = let (v, p) = (head ls)
                             val = "\"" ++ (recoverValues v) ++ "\""
                             prob = "\"" ++ (show (probToReal p)) ++ "\""
                             tl = recoverD2FromList s (tail ls)
                          in if tl /= "" 
                             then (spaceGen s) ++ val ++ ":" ++ prob ++ ",\n" ++ tl
                             else (spaceGen s) ++ val ++ ":" ++ prob

-- Unpacking worlds
recoverD1FromList :: Integer -> Integer -> [((Dist Value), Prob)] -> (String,String)
recoverD1FromList s id [] = ("","")
recoverD1FromList s id ls = let ((D hdl), p) = (head ls)
                                hd = recoverD2FromList (s + 4) (M.assocs hdl)
                                (tl, tlp) = recoverD1FromList s (id + 1) (tail ls)
                                h1 = (spaceGen s) ++ "\"world " ++ (show id) ++ "\":{\n"
                                h2 = h1 ++ (spaceGen (s + 4)) ++ "\"type\":\"Inner\",\n"
                                h3 = h2 ++ hd ++ "\n" ++ (spaceGen s) ++ "}"
                                p1 = (spaceGen (s + 4)) ++ "\"world " ++ (show id) ++ "\":"
                                p2 = p1 ++ "\"" ++ (show (probToReal p)) ++ "\""
                             in if tl /= ""
                                then ((h3 ++ ",\n" ++ tl), (p2 ++ ",\n" ++ tlp))
                                else (h3, p2)

createProbField :: Integer -> String -> String
createProbField s probs = let p1 = (spaceGen s) ++ "\"type\":\"Outer\",\n" 
                              p2 = p1 ++ (spaceGen s) ++ "\"probabilities\":{\n" ++ probs
                              p3 = p2 ++ "\n" ++ (spaceGen s) ++ "}"
                           in p3 

variableDomain :: Integer -> Dist (Dist Value) -> String
variableDomain s hyper = let (D d1) = hyper
                             (worlds, probs) = recoverD1FromList s 1 (M.assocs d1)
                             probField = createProbField s probs
                             variable = probField ++ ",\n" ++ worlds
                          in variable

variableJson :: Integer -> [(String, (Dist (Dist Value)))] -> String
variableJson s [] = ""
variableJson s values = let (var, hyper) = head values
                            tlVar = variableJson s (tail values)
                            hdDomain = variableDomain (s + 4) hyper
                         in if tlVar /= "" 
                            then ((variableLabel s var hdDomain) ++ ",\n" ++ tlVar)
                            else (variableLabel s var hdDomain)

jsonName :: String -> String
jsonName name = let basename = init (init (init (name)))
                 in (basename ++ "_read.json")


createJson1 :: String -> [(String, (Dist (Dist Value)))] -> IO ()
createJson1 fName values = do let s = 4
                              let p1 = "{\n" ++ (spaceGen s) ++ "\"filename\":"
                              let p2 = p1 ++ "\"" ++ fName ++ "\",\n"
                              let p3 = p2 ++ (spaceGen s) ++ "\"variables\":{\n"
                              let p4 = p3 ++ (variableJson (s + 4) values) ++ "\n" 
                              let p5 = p4 ++ (spaceGen s) ++ "}\n" ++ "}"
                              let jName = jsonName fName
                              jsonFile <- openFile jName WriteMode
                              hPutStrLn jsonFile p5
                              hClose jsonFile 
                       
-------------------------------------------------------------------------------
--                  Dense JSON format supported
-------------------------------------------------------------------------------

jsonName2 :: String -> String
jsonName2 name = let basename = init (init (init (name)))
                 in (basename ++ "_mach.json")


-- Unpacking values
recoverDomainValue :: [(Value, Prob)] -> [(String,Prob)]
recoverDomainValue [] = []
recoverDomainValue ls = let (v, _) = (head ls)
                            val = (recoverValues v)
                            tl = recoverDomainValue (tail ls)
                         in if tl /= []
                            then [(val,0.0)] ++ tl
                            else [(val,0.0)]

-- Unpacking worlds
recoverDomainDist :: [((Dist Value), Prob)] -> [(String,Prob)]
recoverDomainDist [] = []
recoverDomainDist ls = let ((D hdl), _) = (head ls)
                           hd = recoverDomainValue (M.assocs hdl)
                           tl = recoverDomainDist (tail ls)
                        in if tl /= []
                           then hd ++ tl
                           else hd

-- Unpacking values
recoverInner :: [(Value, Prob)] -> (M.Map String Prob) -> (M.Map String Prob)
recoverInner [] mp = mp
recoverInner ls mp = let (v, p) = (head ls)
                         val = (recoverValues v)
                         newMp = M.insert val p mp
                         newMp2 = recoverInner (tail ls) newMp
                      in newMp2

-- Unpacking worlds
recoverOuter :: [((Dist Value), Prob)] -> (M.Map String Prob) -> (M.Map (M.Map String Prob) Prob) -> (M.Map (M.Map String Prob) Prob)
recoverOuter [] refMp mp = mp
recoverOuter ls refMp mp = let ((D hd), p) = (head ls)
                               key = recoverInner (M.assocs hd) refMp
                               newMp = M.insert key p mp
                               newMp2 = recoverOuter (tail ls) refMp newMp
                            in newMp2

convertListToString :: [String] -> String
convertListToString [] = ""
convertListToString ls = let hd = "\"" ++ (head ls) ++ "\""
                             tl = convertListToString (tail ls)
                          in if tl /= ""
                             then hd ++ ", " ++ tl
                             else hd

convertProbListToString :: [Prob] -> String
convertProbListToString [] = ""
convertProbListToString ls = let hd = "\"" ++ (show (probToReal (head ls))) ++ "\""
                                 tl = convertProbListToString (tail ls)
                              in if tl /= ""
                                 then hd ++ ", " ++ tl
                                 else hd

createDomainField2 :: Integer -> (M.Map String Prob) -> String
createDomainField2 s mp = let keyList = M.keys mp
                              dstr = convertListToString keyList
                           in (spaceGen s) ++ "\"domain\": [" ++ dstr ++ "]"

createDistField2 :: (M.Map String Prob) -> String
createDistField2 mp = let probList = M.elems mp
                          dstr = convertProbListToString probList
                       in "[" ++ dstr ++ "]"

createListField2 :: [(M.Map String Prob)] -> String
createListField2 [] = ""
createListField2 ls = let hd = createDistField2 (head ls)
                          tl = createListField2 (tail ls)
                       in if tl /= ""
                           then hd ++ ", " ++ tl
                           else hd

createDistHyper2 :: (M.Map (M.Map String Prob) Prob) -> String
createDistHyper2 mp = let probList = M.elems mp
                          dstr = convertProbListToString probList
                       in "[" ++ dstr ++ "]"

createHyperField2 :: Integer -> (M.Map (M.Map String Prob) Prob) -> String
createHyperField2 s mp = let hyperProbs = createDistHyper2 mp
                             worlds = createListField2 (M.keys mp)
                             s1 = (spaceGen s) ++ "\"hyper\": [ " ++ hyperProbs
                          in s1 ++ ", [ " ++ worlds ++ " ] ]"
                            
variableDomain2 :: Integer -> Dist (Dist Value) -> String
variableDomain2 s hyper = let (D d1) = hyper
                              h = (M.assocs d1)
                              domain = M.fromList (recoverDomainDist h)
                              vars = recoverOuter h domain M.empty
                              dField = createDomainField2 s domain
                              hField = createHyperField2 s vars 
                           in dField ++ ",\n" ++ hField

variableJson2 :: Integer -> [(String, (Dist (Dist Value)))] -> String
variableJson2 s [] = ""
variableJson2 s values = let (var, hyper) = head values
                             tlVar = variableJson2 s (tail values)
                             hdDomain = variableDomain2 (s + 4) hyper
                          in if tlVar /= ""
                             then ((variableLabel s var hdDomain) ++ ",\n" ++ tlVar)
                             else (variableLabel s var hdDomain)

createJson2 :: String -> [(String, (Dist (Dist Value)))] -> IO ()
createJson2 fName values = do let s = 4
                              let jContent = "{\n" ++ (variableJson2 s values) ++ "\n}"
                              let jName = jsonName2 fName
                              jsonFile <- openFile jName WriteMode
                              hPutStrLn jsonFile jContent
                              hClose jsonFile
