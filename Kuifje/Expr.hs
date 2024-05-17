{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Expr where 

import qualified Kuifje.Env as E
import Kuifje.Value
import Kuifje.Parse
import Kuifje.Syntax 

import Control.Applicative
import Control.Lens hiding (Profunctor)
import Data.List
import qualified Data.Map as Map
import Data.Map.Strict
import Data.Ratio
import Data.Semigroup
import qualified Data.Set as DSET
import Numeric
import System.IO
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

import Language.Kuifje.Distribution
import Language.Kuifje.PrettyPrint 
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax


(*^*) :: (RealFrac a, RealFrac b) => a -> b -> a
x *^* y = realToFrac $ realToFrac x ** realToFrac y

aOperatorWarpper op (R x) (R y) = 
        case op of 
          Add      -> R $ (+) x y
          Subtract -> R $ (-) x y
          Multiply -> R $ (*) x y
          Divide   -> R $ (/) x y
          Pow      -> R $ x *^* y 
          IDivide  -> R $ (div (truncate x) (truncate y)) % 1
          Rem      -> R $ (rem (truncate x) (truncate y)) % 1

aOperatorWarpper op (T x) (S y) =
        case op of
          Filter    -> S $ DSET.filter (\n -> if (isText n)
                                              then let (T v) = n
                                                    in isSubsequenceOf x v
                                              else False) y
          otherwise -> error "Unknow set operation"

aOperatorWarpper op (R x) (S y) =
        case op of
          Filter    -> S $ DSET.filter (\n -> if (isRational n)
                                              then let (R v) = n
                                                    in (x == v)
                                              else False) y
          otherwise -> error "Unknow set operation"

aOperatorWarpper op (B x) (S y) =
        case op of
          Filter    -> S $ DSET.filter (\n -> if (isBool n)
                                              then let (B v) = n
                                                    in (x == v)
                                              else False) y
          otherwise -> error "Unknow set operation"

aOperatorWarpper op (S x) (S y) = 
        case op of 
          Add      -> S $ DSET.union x y
          Subtract -> let el = x DSET.\\ y
                       in S $ el
          Intersection -> S $ DSET.intersection x y
          Filter    -> S $ DSET.filter (\n -> if (isSet n)
                                              then let (S v) = n
                                                    in DSET.isSubsetOf x v
                                              else False) y
          otherwise -> error "Unknow set operation"

aOperatorWarpper op a b = error ("Unknow operation " ++ (show op) ++ " <> " ++ (show a) ++ " <> " ++ (show b))

aOperator op d1 d2 = 
  D $ fromListWith (+) [((aOperatorWarpper op x y), p * q) | (x, p) <- toList $ runD d1,
                                                             (y, q) <- toList $ runD d2]

cOperatorWarpper Lt (R x) (R y) = (x < y)
cOperatorWarpper Gt (R x) (R y) = (x > y)
cOperatorWarpper Le (R x) (R y) = (x <= y)
cOperatorWarpper Ge (R x) (R y) = (x >= y)
cOperatorWarpper Eq (R x) (R y) = (x == y)
cOperatorWarpper Ne (R x) (R y) = (x /= y)

cOperatorWarpper IsSubstrOf (T x) (T y) = (isSubsequenceOf x y)
cOperatorWarpper Eq (T x) (T y) = ((isInfixOf x y) && (isInfixOf y x))
cOperatorWarpper Ne (T x) (T y) = (not ((isInfixOf x y) && (isInfixOf y x)))

cOperatorWarpper op v1 v2 =
  error ("Operator: " ++ show op ++ " not found for " ++ valuePrettyType v1 ++ " vs. " ++ valuePrettyType v2)

cOperator op d1 d2 =
  D $ fromListWith (+) [((B (cOperatorWarpper op x y)), p * q) | (x, p) <- toList $ runD d1,
                                                                 (y, q) <- toList $ runD d2]
bOperator op d1 d2 = 
  D $ fromListWith (+) [((B (op x y)), p * q) | (B x, p) <- toList $ runD d1,
                                                (B y, q) <- toList $ runD d2]

createSetList [] = []
createSetList ls =
  let hd = head ls
      tl = createSetList (tail ls)
   in (S hd) : tl

setValueWarpper (S x) = (S (DSET.fromList (createSetList (DSET.elems (DSET.powerSet x)))))
-- DSET.powerSet x

sOperatorPowerSet d1 =
  D $ fromListWith (+) [((setValueWarpper x), p) | (x, p) <- toList $ runD d1]

sBinOperatorWrapper op (S x) (S y) =
  case op of
    IsSubOf   -> DSET.isSubsetOf x y
    otherwise -> error "Unknow set membership operation"

sBinOperatorWrapper op x (S y) =
  case op of
    In       -> DSET.member x y
    NIn      -> DSET.notMember x y
    otherwise -> error "Unknow set membership operation"

sBinOperatorWrapper op x y =
  case op of
    In       -> (x == y)
    NIn      -> (x /= y)
    otherwise -> error "Unknow set membership operation"

sBinOperator op d1 d2 =
  D $ fromListWith (+) [((B (sBinOperatorWrapper op x y)), p * q) | (x, p) <- toList $ runD d1,
                                                                    (y, q) <- toList $ runD d2]
updateProbs :: [(Prob, Value)] -> Prob -> [(Prob, Value)]
updateProbs [] _ = []
updateProbs ls p = let hd = head ls
                       tl = tail ls
                       pEl = fst hd
                       el = snd hd
                       newP = pEl * p
                       newEl = (newP, el)
                       newList = updateProbs tl p
                    in newEl : newList

createNewDist :: Value -> Value -> Prob -> Value
createNewDist (PD s1) (PD s2) p = 
   let el1 = DSET.elems s1
       el2 = DSET.elems s2
       newEl1 = updateProbs el1 p
       newEl2 = updateProbs el2 (1-p)
       newList = newEl1 ++ newEl2
    in (PD (DSET.fromDistinctAscList newList))
createNewDist (PD s1) v2 p =
   let el1 = DSET.elems s1
       newEl1 = updateProbs el1 p
       newEl2 = [((1-p), v2)]
       newList = newEl1 ++ newEl2
    in (PD (DSET.fromDistinctAscList newList))
createNewDist v1 (PD s2) p =
   let el2 = DSET.elems s2
       newEl2 = updateProbs el2 (1-p)
       newEl1 = [(p, v1)]
       newList = newEl1 ++ newEl2
    in (PD (DSET.fromDistinctAscList newList))
createNewDist v1 v2 p = 
   let newEl1 = [(p, v1)]
       newEl2 = [((1-p), v2)]
       newList = newEl1 ++ newEl2
    in (PD (DSET.fromDistinctAscList newList))

extractFromListTy :: Value -> [Value]
extractFromListTy (LS list) = list
extractFromListTy e = error ("The Instruction:\n" ++ (show e) ++ "\n is not accesed by index!")

distFromMapVals :: [(Value, Prob)] -> [(Prob, Value)]
distFromMapVals [] = []
distFromMapVals ls = let (v, p) = (head ls)
                         tl = distFromMapVals (tail ls)
                      in (p, v) : tl

recoverElemFromList :: [Value] -> Integer -> Value
recoverElemFromList [] _ = error ("Element out of index!")
recoverElemFromList ls id = if (id == 0)
                            then (head ls)
                            else (recoverElemFromList (tail ls) (id - 1))

insertElemIntoList :: [Value] -> Value -> Integer -> [Value]
insertElemIntoList [] el 0 = [el]
insertElemIntoList [] el _ = error ("Element out of index!")
insertElemIntoList ls el id = if (id == 0)
                              then [el] ++ ls
                              else [(head ls)] ++ (insertElemIntoList (tail ls) el (id - 1)) 

removeElemFromList :: [Value] -> Value -> Bool -> [Value]
removeElemFromList [] el False = error ((show el) ++ ".remove(x): x not in list")
removeElemFromList ls el False = let hd = head ls
                                     tl = tail ls
                                  in if (hd == el)
                                     then removeElemFromList tl el True
                                     else ([hd] ++ (removeElemFromList tl el False))
removeElemFromList ls _ True = ls

lenghtFromList :: [Value] -> Integer
lenghtFromList [] = 0
lenghtFromList ls = (1 + (lenghtFromList (tail ls)))

exprToValue2Cntx :: Expr -> (Dist Value) -> (Dist Value) -> Value
exprToValue2Cntx (ListExtend id list) ev1 ev2 = 
  let ls1 = fst (head (assocs (unpackD ev1)))
      el1 = extractFromListTy ls1
      ls2 = fst (head (assocs (unpackD ev2)))
      el2 = extractFromListTy ls2
      newL = el1 ++ el2
   in (LS newL)
exprToValue2Cntx (ListElem lsid index) ev1 ev2 =
  let ls = fst (head (assocs (unpackD ev1)))
      ind = fst (head (assocs (unpackD ev2)))
      elems = extractFromListTy ls
   in if (isRational ind)
      then let (R id) = ind
            in recoverElemFromList elems (numerator id)
      else error ("Out of range access index in list: " ++ (show lsid)) 
exprToValue2Cntx (ListElemDirect list index) ev1 ev2 =
  let ls = fst (head (assocs (unpackD ev1)))
      ind = fst (head (assocs (unpackD ev2)))
      elems = extractFromListTy ls
   in if (isRational ind)
      then let (R id) = ind
            in recoverElemFromList elems (numerator id)
      else error ("Out of range access index in list: " ++ (show list))
exprToValue2Cntx (ListAppend id elem) ev1 ev2 =
  let ls = fst (head (assocs (unpackD ev1)))
      el = fst (head (assocs (unpackD ev2)))
      elems = extractFromListTy ls
      newL = elems ++ [el]
   in (LS newL)
exprToValue2Cntx (ListInsert id index elem) ev1 ev2 =
  let ls = fst (head (assocs (unpackD ev1)))
      el = fst (head (assocs (unpackD ev2)))
      elems = extractFromListTy ls
      id = exprToValue index ev1
   in if (isRational id)
         then let (R ind) = id
                  newL = insertElemIntoList elems el (numerator ind)
               in (LS newL)
         else error ("Invalid index" ++ (show index))


exprToValue :: Expr -> (Dist Value) -> Value
--exprToValue (Var id) ev = let vals = distFromMapVals (assocs (unpackD ev))
--                           in  (PD (DSET.fromDistinctAscList vals))
                           --in if ((length vals) == 1)
                           --   then (snd (head (vals)))
                           --   else (PD (DSET.fromDistinctAscList vals))
exprToValue (RationalConst r) _ = (R r)
exprToValue (Text t) _ = (T t)
exprToValue (Neg a) ev = exprToValue (ABinary Multiply (RationalConst (-1 % 1)) a) ev
exprToValue (BoolConst b) _ = (B b)
exprToValue (ABinary Multiply (RationalConst a) (RationalConst b)) _ = (R (a * b))
exprToValue (ABinary Divide (RationalConst a) (RationalConst b)) _ = (R (a / b))
exprToValue (Eset ns) ev = 
   let e = DSET.elems ns
       l = lExprTolValues e ev
       s = DSET.fromList l
    in (S s)
exprToValue (IchoiceDist e1 e2 p) ev =
   let v1 = exprToValue e1 ev
       v2 = exprToValue e2 ev
       (R r) = exprToValue p ev
       p2 = (1 - r)
       list = [(r, v1), (p2, v2)]
    in (PD (DSET.fromDistinctAscList list))
exprToValue (ListExpr ls) ev =
  let l = lExprTolValues ls ev
   in (LS l)
exprToValue (ListInsert id index elem) ev =
  let ls = fst (head (assocs (unpackD ev)))
      elems = extractFromListTy ls
      el = exprToValue elem ev
      id = exprToValue index ev
   in if (isRational id)
         then let (R ind) = id
                  newL = insertElemIntoList elems el (numerator ind)
               in (LS newL)
         else error ("Invalid index" ++ (show index))
exprToValue (ListRemove id elem) ev =
  let ls = fst (head (assocs (unpackD ev)))
      elems = extractFromListTy ls
      el = exprToValue elem ev
      newL = removeElemFromList elems el False
   in (LS newL)
exprToValue (ListLength list) ev =
  let ls = fst (head (assocs (unpackD ev)))
      elems = extractFromListTy ls
      r = lenghtFromList elems
   in (R (r % 1))
exprToValue (TupleExpr ls) ev =
  let l = lExprTolValues ls ev
   in (TP l)
exprToValue e _ = error ("Invalid exprToValue:\n" ++ (show e))

lExprTolValues :: [Expr] -> (Dist Value) -> [Value]
lExprTolValues [] _ = []
lExprTolValues ls ev =
        let hd = exprToValue (head ls) ev
            tl = lExprTolValues (tail ls) ev
         in hd : tl

createDistList :: Prob -> [Expr] -> (Dist Value) -> [(Prob, Value)]
createDistList _ [] _ = []
createDistList prob ls ev = let hd = exprToValue (head ls) ev
                                tl = createDistList prob (tail ls) ev
                             in [(prob, hd)] ++ tl

convertTuple :: Expr -> (Prob, Value)
convertTuple (Tuple e p) = let ev = (evalE (RationalConst (0 % 1))) E.empty
                               val = exprToValue e ev
                               (R pr) = exprToValue p ev
                            in (pr, val)

convertINUlist :: [Expr] -> [(Prob, Value)]
convertINUlist [] = []
convertINUlist ls = let hd = convertTuple (head ls)
                        tl = convertINUlist (tail ls)
                     in hd : tl

convertDistListToExprList :: [(Prob, Value)] -> [Expr]
convertDistListToExprList [] = []
convertDistListToExprList ls = let (p, v) = head ls
                                   newE = valueToExpr v
                                   newP = valueToExpr (R p)
                                   tl = convertDistListToExprList (tail ls)
                                   tuple = (Tuple newE newP)
                                in tuple : tl

convertTupleListToExpr :: [Expr] -> Expr
convertTupleListToExpr ls = if (length ls) == 1
                            then let (Tuple eHead _) = (head ls)
                                  in eHead
                            else let (Tuple eHead p) = (head ls)
                                     eTail = convertTupleListToExpr (tail ls)
                                  in (Ichoice eHead eTail p)

convertDistToExpr :: Value -> Expr
convertDistToExpr (PD s) = let expL = convertDistListToExprList (DSET.elems s)
                            in convertTupleListToExpr expL

sampleFromDistList :: [Expr] -> [Expr]
sampleFromDistList [] = []
sampleFromDistList ls = let hd = sampleFromDist (head ls)
                            tl = sampleFromDistList (tail ls)
                         in hd : tl

sampleFromDist :: Expr -> Expr
-- Primitive Values
sampleFromDist (Var id) = (Var id)
sampleFromDist (RationalConst r) = (RationalConst r) 
sampleFromDist (Text t) = (Text t)
sampleFromDist (Neg r) = (Neg r)
sampleFromDist (BoolConst b) = (BoolConst b)
sampleFromDist (Not b) = (Not b)
sampleFromDist (Geometric alpha low start high) = (Geometric alpha low start high)
-- Complex Values (including set)
sampleFromDist (Eset set) = let newL = sampleFromDistList (DSET.elems set)
                                newSet = DSET.fromList newL
                             in (Eset newSet)
sampleFromDist (ExprIf cond e1 e2) = let newE1 = sampleFromDist e1
                                         newE2 = sampleFromDist e2
                                      in (ExprIf cond newE1 newE2) 
sampleFromDist (ABinary op e1 e2) = let newE1 = sampleFromDist e1
                                        newE2 = sampleFromDist e2
                                     in (ABinary op e1 e2)
sampleFromDist (Ichoice e1 e2 p) = let newE1 = sampleFromDist e1
                                       newE2 = sampleFromDist e2
                                    in (Ichoice newE1 newE2 p)
sampleFromDist (IchoiceDist e1 e2 p) = let newE1 = sampleFromDist e1
                                           newE2 = sampleFromDist e2
                                        in (Ichoice newE1 newE2 p)
sampleFromDist (Ichoices ls) = let newLs = sampleFromDistList ls
                                in (Ichoices newLs)
sampleFromDist (IchoicesDist ls) = let newLs = sampleFromDistList ls
                                    in (Ichoices newLs)
sampleFromDist (Tuple e p) = let newE = sampleFromDist e
                              in (Tuple newE p)
sampleFromDist (INUchoices ls) = let newLs = sampleFromDistList ls
                                  in (INUchoices newLs)
sampleFromDist (INUchoicesDist ls) = let newLs = sampleFromDistList ls
                                      in (INUchoices newLs)
sampleFromDist (PowerSet e) = let newE = sampleFromDist e
                               in (PowerSet newE)
sampleFromDist (SBinary op e1 e2) = let newE1 = sampleFromDist e1
                                        newE2 = sampleFromDist e2
                                     in (SBinary op newE1 newE2)
sampleFromDist (BBinary op e1 e2) = let newE1 = sampleFromDist e1
                                        newE2 = sampleFromDist e2
                                     in (BBinary op newE1 newE2)
sampleFromDist (RBinary op e1 e2) = let newE1 = sampleFromDist e1
                                        newE2 = sampleFromDist e2
                                     in (RBinary op newE1 newE2)
sampleFromDist (SetIchoice e) = let newE = sampleFromDist e
                                 in (SetIchoice newE)
sampleFromDist (SetIchoiceDist e) = let newE = sampleFromDist e
                                     in (SetIchoice newE)
sampleFromDist (ListExpr ls) = (INUchoices ls)
--sampleFromDist (ListExpr ls) = let newLs = convertTupleListToExpr ls
--                                in error ("List is: " ++ show (newLs))
sampleFromDist e = error("Error: " ++ show(e))

isTuple :: Expr -> Bool
isTuple (Tuple _ _) = True
isTuple _ = False

isTupleList :: [Expr] -> Bool
isTupleList [] = False
isTupleList ls = isTuple (head ls)

evalE :: Expr -> (Gamma ~> Value)
evalE (Var id) = \s -> case E.lookup s id of 
                          Just v -> returnDist v
                          otherwise -> error ("Variable " ++ id ++ " not in scope")
evalE (RationalConst r) = \s -> returnDist (R r)
evalE (Text t) = \s -> returnDist (T t)
evalE (Neg r) = \s -> 
        let r' = (evalE r) s in 
            (fmapDist (\p -> case p of 
                           (R p') -> R (-1 * p'))) r'
evalE (ExprIf cond e1 e2) = \s -> 
        let cond' = runD $ (evalE cond) s
            e1' = (evalE e1) s
            e2' = (evalE e2) s 
            d1 = case Data.Map.Strict.lookup (B True) cond' of 
                   (Just p)  -> D $ Data.Map.Strict.map (*p) $ runD e1'
                   otherwise -> D $ Data.Map.Strict.empty
            d2 = case Data.Map.Strict.lookup (B False) cond' of 
                   (Just p)  -> D $ Data.Map.Strict.map (*p) $ runD e2'
                   otherwise -> D $ Data.Map.Strict.empty
         in D $ unionWith (+) (runD d1) (runD d2)
evalE (ABinary op e1 e2) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s 
   in aOperator op e1' e2' 
evalE (Ichoice e1 e2 p) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s 
      p'  = Data.List.foldr (\x y -> case x of (R x', q) -> x'*q*y) 1 
              $ toList $ runD $ (evalE p ) s
      d1 = D $ Data.Map.Strict.map (*p') $ runD e1'
      d2 = D $ Data.Map.Strict.map (*(1-p')) $ runD e2'
   in D $ unionWith (+) (runD d1) (runD d2)
evalE (IchoiceDist e1 e2 p) = \s ->
  let dw = fmapDist theRational $ evalE p s
   in bindDist dw (joinDist . bernoulli (evalE e1 s) (evalE e2 s))
evalE (Ichoices ls) = 
   if length ls == 1 
      then evalE $ head ls
      else evalE $ Ichoice 
                          (head ls) 
                          (Ichoices (tail ls)) 
                          (RationalConst (1 % (toInteger (length ls))))
evalE (IchoicesDist ls) = \s -> 
   let ev = (evalE (Ichoices ls)) s
       p = (1 % (toInteger (length ls)))
       vals = createDistList p ls ev
       dist = (PD (DSET.fromDistinctAscList vals))
    in returnDist dist
evalE (Tuple e p) = \s ->
  let e' = (evalE e) s
      p' = Data.List.foldr (\x y -> case x of (R x', q) -> x'*q*y) 1
              $ toList $ runD $ (evalE p) s
      d = D $ Data.Map.Strict.map (*p') $ runD e'
   in D $ (runD d)
evalE (INUchoices ls) =
  if (evalTList $ INUchoices ls) == 1.0
     then evalNUList $ INUchoices ls
     else error ("Probability adds up to: " ++ 
          (show (evalTList $ INUchoices ls)) ++
          " --> It should be 1.0" )
evalE (INUchoicesDist ls) = \s ->
  if (evalTList $ INUchoicesDist ls) == 1.0
     then let vals = convertINUlist ls
              dist = (PD (DSET.fromDistinctAscList vals))
           in returnDist dist
     else error ("Probability adds up to: " ++ 
          (show (evalTList $ INUchoicesDist ls)) ++
          " --> It should be 1.0" )
evalE (BoolConst b) = \s -> returnDist (B b)
evalE (PowerSet e1) = \s -> 
       let s' = (evalE e1) s in
           sOperatorPowerSet s'
evalE (Not b) = \s -> 
        let r' = (evalE b) s 
         in (fmapDist (\bv -> case bv of 
                            (B b') -> B (not b'))) r'
evalE (SBinary op e1 e2) = \s ->
  let e1' = (evalE e1) s
      e2' = (evalE e2) s in
      sBinOperator op e1' e2'
evalE (BBinary op e1 e2) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s in 
      case op of 
        And -> (bOperator (&&) e1' e2') -- /\
        Or  -> (bOperator (||) e1' e2') -- \/
evalE (RBinary op e1 e2) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s in 
      cOperator op e1' e2'
evalE (Eset set) = \s -> 
        let exprToValue elem = toList (runD ((evalE elem) s))
            distList = Data.List.map exprToValue (DSET.toList set) 
            tmpf2 :: (Value, Prob) -> (Value, Prob) -> (Value, Prob)
            tmpf2 (S a, b) (c, d) = (S (DSET.insert c a), b*d)
            -- helperFun :: [()]
            helperFun x y = liftA2 tmpf2 y x
            init :: [(Value, Prob)]
            init = [(S DSET.empty, 1)]
            resultList :: [(Value, Prob)]
            resultList = Data.List.foldr helperFun init distList
         in D $ fromListWith (+) resultList
evalE (SetIchoice e) = \s -> 
        let d = (evalE e) s 
            resultList = concat [[(elem, p/(toInteger (DSET.size set) % 1)) 
                                        | elem <- DSET.toList set] 
                                        | (S set, p) <- toList (runD d)]
         in D $ fromListWith (+) resultList
evalE (SetIchoiceDist e) = \s -> 
        let d = (evalE e) s
            resultList = concat [[(p/(toInteger (DSET.size set) % 1), elem)
                                        | elem <- DSET.toList set]
                                        | (S set, p) <- toList (runD d)]
            dist = (PD (DSET.fromDistinctAscList resultList))
         in returnDist dist
evalE (Geometric alpha low start high) =
         let alphaV = evalTList $ alpha
             lowV = round (evalTList $ low)
             highV = round (evalTList $ high)
             startV = round (evalTList $ start)
             interprobs = [(calcGeom alphaV startV x) | x <- [(lowV+1)..(highV-1)]]
             lowLimit = calcLimitGeom alphaV startV lowV
             highLimit = calcLimitGeom alphaV startV highV
             values = [x | x <- [lowV .. highV]]
             probs = [lowLimit] ++ interprobs ++ [highLimit]
             sProbs = sum probs
             resultDist = buildDist values probs
         in evalNUList $ INUchoices resultDist
evalE (ListExpr []) = \s -> returnDist (LS []) 
evalE (ListExpr list) = \s ->  
         let els = evalE (ListExpr []) s
          in if (isTupleList list) == True
             then evalE (INUchoicesDist list) s
             else let ls = exprToValue (ListExpr list) els
                  in returnDist ls
evalE (ListElem id index) = \s -> 
         let ev1 = evalE (Var id) s
             ev2 = evalE index s
             el = exprToValue2Cntx (ListElem id index) ev1 ev2
          in returnDist el
evalE (ListElemDirect list index) = \s ->
         let ev1 = evalE (ListExpr list) s
             ev2 = evalE index s
             el = exprToValue2Cntx (ListElemDirect list index) ev1 ev2
          in returnDist el
evalE (ListAppend id elem) = \s ->
         let ev1 = evalE (Var id) s
             ev2 = evalE elem s
             el = exprToValue2Cntx (ListAppend id elem) ev1 ev2
          in returnDist el
evalE (ListInsert id index elem) = \s ->
         let ev1 = evalE (Var id) s
             ev2 = evalE elem s
             el = exprToValue2Cntx (ListInsert id index elem) ev1 ev2
          in returnDist el
evalE (ListExtend id1 id2) = \s ->
         let ev1 = evalE (Var id1) s
             ev2 = evalE (Var id2) s
             el = exprToValue2Cntx (ListExtend id1 id2) ev1 ev2
          in returnDist el
evalE (ListRemove id elem) = \s ->
         let elist = evalE (Var id) s
             el = exprToValue (ListRemove id elem) elist
          in returnDist el
evalE (ListLength list) = \s ->
         let elist = evalE list s
             el = exprToValue (ListLength list) elist
          in returnDist el
--evalE (TupleExpr []) = \s -> returnDist (TP []) 
--evalE (TupleExpr list) = \s ->
--         let hd = evalE (head list) s
--             tl = evalE (TupleExpr (tail list)) s
--          in D $ fromListWith (+) resultList
evalE (TupleExpr list) = \s -> 
        let runAll e = toList (runD ((evalE e) s))
            distList = Data.List.map runAll list
            tmpDistToVal :: [(Value, Prob)] -> [Value]
            tmpDistToVal [] = []
            tmpDistToVal ls =
                         let hd = head ls
                             (a, _) = hd
                             tl = tmpDistToVal (tail ls)
                          in [a] ++ tl
            valList = Data.List.map tmpDistToVal distList
            to1DList :: [[Value]] -> [Value]
            to1DList [] = []
            to1DList ls =
                     let hd = head ls
                         tl = to1DList (tail ls)
                      in hd ++ tl
            linearList = to1DList valList
         in returnDist (TP linearList)

buildDist :: [Integer] -> [Rational] -> [Expr]
buildDist [] [] = []
buildDist values probs = 
         let value = head values
             prob = head probs
             tl = buildDist (tail values) (tail probs)
          in (Tuple (RationalConst (value % 1)) (RationalConst prob)) : tl

calcLimitGeom :: Double -> Integer -> Integer -> Rational
calcLimitGeom alpha start bound = realToFrac ((1 / (1 + alpha)) * (alpha^(abs (bound - start))))

calcGeom :: Double -> Integer -> Integer -> Rational
calcGeom alpha start n = realToFrac (((1 - alpha) / (1 + alpha)) * (alpha^(abs (n - start))))

evalTList :: Expr -> Double
evalTList (RationalConst a) = (fromRat a)
evalTList (Neg a) = -1 * (evalTList a)
evalTList (ABinary Divide a b) = 
  let aVal = (evalTList $ a)
      bVal = (evalTList $ b)
  in ( aVal / bVal)
evalTList (Tuple _ p) = evalTList $ p
evalTList (INUchoices []) = 0.0
evalTList (INUchoices ls) = 
  let hd = (evalTList $ head ls)
      tl = (evalTList $ INUchoices (tail ls))
  in hd + tl
evalTList (INUchoicesDist []) = 0.0
evalTList (INUchoicesDist ls) =
  let hd = (evalTList $ head ls)
      tl = (evalTList $ INUchoicesDist (tail ls))
  in hd + tl

recoverIChoicesValues :: Expr -> [Expr]
recoverIChoicesValues (RationalConst x) = [(RationalConst x)]
recoverIChoicesValues (Ichoice v1 v2 _) =
  let hd = (recoverIChoicesValues v1)
      tl = (recoverIChoicesValues v2)
   in hd ++ tl
recoverIChoicesValues x = error ("Distribution to Value fail to:\n" ++ (show x) ++ "\n\n")

evalNUList (INUchoices ls) =
  if length ls == 1
     then evalE $ head ls
     else \s ->
        let e1' = (evalE $ head ls) s
            e2' = (evalNUList $ INUchoices (tail ls)) s
         in D $ unionWith (+) (runD e1') (runD e2')

fromJustExpr :: Maybe Expr -> Expr
fromJustExpr (Just a) = a
fromJustExpr Nothing = error "Function not found."

getCntxExpr :: String -> Map.Map String Expr -> Expr
getCntxExpr id fCntx = fromJustExpr (Map.lookup id fCntx)

lValuesTolExpr :: [Value] -> [Expr]
lValuesTolExpr [] = []
lValuesTolExpr ls =
        let hd = valueToExpr (head ls)
            tl = lValuesTolExpr (tail ls)
         in hd : tl

valueToExpr :: Value -> Expr
valueToExpr (R r) = (RationalConst r)
valueToExpr (T t) = (Text t)
valueToExpr (B b) = (BoolConst b)
valueToExpr (S s) =
        let e = DSET.elems s
            l = lValuesTolExpr e
            ns = DSET.fromList l
         in (Eset ns)
valueToExpr (PD s) =
        let ls = DSET.elems s
            e = convertDistListToExprList ls
         in (INUchoicesDist e)

