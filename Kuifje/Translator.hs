{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Translator where 

import qualified Kuifje.Env as E
import qualified Data.Map as Map
import Kuifje.Value
import Kuifje.Parse
import Kuifje.Syntax 

import Prelude hiding ((!!), return, fmap, (>>=))
import Control.Lens hiding (Profunctor)
import Data.Semigroup
import Data.Ratio
import Data.Map.Strict
import Data.List
import qualified Data.Set as DSET
import Numeric

import Language.Kuifje.Distribution
--import Kuifje.PrettyPrint 
import Language.Kuifje.PrettyPrint 
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Control.Applicative

import System.IO 
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

(*^*) :: (RealFrac a, RealFrac b) => a -> b -> a
x *^* y = realToFrac $ realToFrac x ** realToFrac y

isText :: Value -> Bool
isText (T _) = True
isText _ = False

isSet :: Value -> Bool
isSet (S _) = True
isSet _ = False

isBool :: Value -> Bool
isBool (B _) = True
isBool _ = False

isRational :: Value -> Bool
isRational (R _) = True
isRational _ = False

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
                       in if ((DSET.size el) > 1)
                          then S $ el
                          else (head (DSET.elems el))
          Intersection -> S $ DSET.intersection x y
          Filter    -> S $ DSET.filter (\n -> if (isSet n)
                                              then let (S v) = n
                                                    in DSET.isSubsetOf x v
                                              else False) y
          otherwise -> error "Unknow set operation"

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

cOperatorWarpper op v1 v2 = error ("Operator: " ++ (show op) ++ " Not found!\n" ++ (show v1) ++ "\n" ++ (show v2))

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

distFromMapVals :: [(Value, Prob)] -> [(Prob, Value)]
distFromMapVals [] = []
distFromMapVals ls = let (v, p) = (head ls)
                         tl = distFromMapVals (tail ls)
                      in (p, v) : tl

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
                            then (head ls)
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

evalE :: Expr -> (Gamma ~> Value)
evalE (Var id) = \s -> case E.lookup s id of 
                          Just v -> (return v)
                          otherwise -> error ("Variable " ++ id ++ " not in scope")
evalE (RationalConst r) = \s -> return (R r)
evalE (Text t) = \s -> return (T t)
evalE (Neg r) = \s -> 
        let r' = (evalE r) s in 
            (fmap (\p -> case p of 
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
  let v1' = (evalE e1) s
      v2' = (evalE e2) s
      p' = (evalE p) s
      v1 = exprToValue e1 v1'
      v2 = exprToValue e2 v2'
      (R r) = exprToValue p p'
      dist = createNewDist v1 v2 r
   in return dist
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
    in return dist
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
           in return dist
     else error ("Probability adds up to: " ++ 
          (show (evalTList $ INUchoicesDist ls)) ++
          " --> It should be 1.0" )
evalE (BoolConst b) = \s -> return (B b)
evalE (PowerSet e1) = \s -> 
       let s' = (evalE e1) s in
           sOperatorPowerSet s'
evalE (Not b) = \s -> 
        let r' = (evalE b) s 
         in (fmap (\bv -> case bv of 
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
--      case op of 
--        Gt -> (cOperator (>) e1' e2')
--        Ge -> (cOperator (>=) e1' e2')
--        Lt -> (cOperator (<) e1' e2')
--        Le -> (cOperator (<=) e1' e2')
--        Eq -> (cOperator (==) e1' e2')
--        Ne -> (cOperator (/=) e1' e2')
--        IsSubstrOf ->  (cOperator (<) e1' e2')
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
         in return dist
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

extractStr :: Expr -> String
extractStr (Text t) = t

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

valuesToExprList :: [(Value, Rational)] -> [Expr]
valuesToExprList [] = []
valuesToExprList ls =
        let hd = head ls
            exp = valueToExpr (fst hd)
            tl = valuesToExprList (tail ls)
         in exp : tl

getSupportList :: [(Dist Value)] -> [Expr]
getSupportList [] = []
getSupportList ls = 
        let hd = assocs (unpackD (head ls))
            newHd = valuesToExprList hd 
            tl = getSupportList (tail ls)
         in newHd ++ tl

getSupportDist :: [((Dist Value), Rational)] -> [(Expr, Rational)]
getSupportDist [] = []
getSupportDist ls =
        let hd = head ls
            exp = valuesToExprList (assocs (unpackD (fst hd)))
            newExp = (Eset (DSET.fromList exp))
            prob = snd hd
            tl = getSupportDist (tail ls)
         --in (newExp, prob) : tl
         in if length exp == 1
            then ((head exp), prob) : tl
            else (newExp, prob) : tl

getSupportFromHyper :: Dist (Dist Value) -> [(Expr, Rational)]
getSupportFromHyper d =
        let mp = unpackD d
         in getSupportDist (assocs mp)

recoverSupportAsDistList :: [(Expr, Rational)] -> [Expr]
recoverSupportAsDistList [] = []
recoverSupportAsDistList ls = 
        let (e, r) = (head ls)
            p = (RationalConst r) 
            tp = (Tuple e p)
            tl = recoverSupportAsDistList (tail ls)
          in tp : tl

getFromDist g s | Just x <- E.lookup g s = x
                | otherwise = error ("Not going to happend " ++ s)

exec :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
exec var = fmap (fmap (\s -> getFromDist s var))

data MonadValue = M (Kuifje Gamma)
           | O Expr
           | A String Expr
           | L [MonadValue]
           | C Expr MonadValue MonadValue
           | E MonadValue MonadValue Expr
           | W Expr MonadValue

monadType :: MonadValue -> String
monadType (A id e) = ("\nAssign: " ++ id ++ " =>> " ++ (show e))
monadType (M md) = ("\nM: Monad")
monadType (O e) = ("\nO: Observe")
monadType (L []) = ""
monadType (L ls) = 
     let hd = monadType (head ls)
         tl = monadType (L (tail ls))
      in ("\n[" ++ hd ++ " <> "++ tl ++ "]")
monadType (C e t f) = ("\nC: \n  T = " ++ (monadType t) ++ "\n  F = " ++ (monadType f)) 
monadType (E t f p) = ("\nE: \n  T = " ++ (monadType t) ++ "\n  F = " ++ (monadType f))
monadType (W e b) = ("\nW: \n  B = " ++ (monadType b))

concatMonadValues :: MonadValue -> MonadValue -> MonadValue
concatMonadValues (L l1) (L l2) = (L (l1 ++ l2))
concatMonadValues v (L l2) = (L (v : l2))
concatMonadValues (L l1) v = (L (l1 ++ [v]))
concatMonadValues v1 v2 = (L ([v1] ++ [v2]))

createMonnad :: MonadValue -> Kuifje Gamma
createMonnad (M m) = m
createMonnad (O e) = observe (evalE e)
createMonnad (A id expr) = 
        Language.Kuifje.Syntax.update (\s -> 
          let currS = (evalE expr) s in
            fmap (\r -> E.add s (id, r)) currS)
createMonnad (L []) = skip
createMonnad (L ls) = createMonnad (head ls) <> createMonnad (L (tail ls))
createMonnad (W e body) =
        Language.Kuifje.Syntax.while (\s -> 
                let currS = (evalE e) s in 
                    fmap (\r -> case r of (B b) -> b) currS) (createMonnad body)
createMonnad (C e s1 s2) =
        Language.Kuifje.Syntax.cond 
          (\s -> let currS = (evalE e) s in fmap (\r -> case r of (B b) -> b) currS) 
          -- (createMonnad s1)
          -- (createMonnad s2)
          --
          -- Leaks the conditional after choose an option
          ((createMonnad s1) <> (observe (evalE e))) 
          ((createMonnad s2) <> (observe (evalE e)))
createMonnad (E s1 s2 p) =
        Language.Kuifje.Syntax.cond
          (\s -> let p' = (evalE (Ichoice (BoolConst True) (BoolConst False) p) s)
                  in (fmap (\r -> case r of (B b) -> b)) p')
          (createMonnad s1)
          (createMonnad s2)

recoverVars :: Expr -> [String] -> [String]
recoverVars (Var id) ls = ([id] ++ ls)
recoverVars (RationalConst _) ls = ls
recoverVars (Text _) ls = ls
recoverVars (IchoicesDist list) ls = 
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (IchoiceDist e1 e2 _) ls = 
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (PowerSet _) ls = ls
recoverVars (Neg r) ls = recoverVars r ls
recoverVars (ExprIf cond e1 e2) ls = 
        let ls1 = recoverVars cond ls
            ls2 = recoverVars e1 ls1
            ls3 = recoverVars e2 ls2
         in ls3
recoverVars (ABinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Ichoice e1 e2 _) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Ichoices list) ls = 
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (Tuple e _) ls = recoverVars e ls
recoverVars (INUchoices list) ls =
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (INUchoicesDist list) ls =
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (BoolConst _) ls =  ls
recoverVars (Not b) ls = recoverVars b ls
recoverVars (SBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (BBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (RBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Eset _) ls = ls
recoverVars (SetIchoice e) ls = recoverVars e ls
recoverVars (SetIchoiceDist e) ls = recoverVars e ls
recoverVars (Geometric _ _ _ _) ls = ls

checkListInMap :: Map.Map String Expr -> [String] -> Bool
checkListInMap m [] = True
checkListInMap m ls =
        let hd = Map.member (head ls) m
            tl = checkListInMap m (tail ls)
         in if hd == False then
            error ("\n\n  Variable (" ++ (head ls) ++ ") not declared before being used.")
           else (hd && tl)

livenessAnalysis :: MonadValue -> Map.Map String Expr -> (Bool, Map.Map String Expr)
livenessAnalysis (M m) vars = (True, vars)
livenessAnalysis (O e) vars = ((checkListInMap vars (recoverVars e [])),vars)
livenessAnalysis (A id e) vars =
        let newVars = Map.insert id e vars
            varList = recoverVars e []
            valid = checkListInMap vars varList
         in (valid, newVars)
livenessAnalysis (L []) vars = (True, vars)
livenessAnalysis (L ls) vars =
        let (hdVal, hdVars) = livenessAnalysis (head ls) vars
            (tlVal, tlVars) = livenessAnalysis (L (tail ls)) hdVars
         in ((hdVal && tlVal), tlVars)
livenessAnalysis (C e t f) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (tVal, _) = livenessAnalysis t vars
            (fVal, _) = livenessAnalysis f vars
         in ((eVal && tVal && fVal), vars)
livenessAnalysis (E t f e) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (tVal, tVars) = livenessAnalysis t vars
            (fVal, fVars) = livenessAnalysis f tVars
         in ((eVal && tVal && fVal), fVars)
livenessAnalysis (W e b) vars =
        let eVal = (checkListInMap vars (recoverVars e []))
            (bVal, bVars) = livenessAnalysis b vars
         in ((eVal && bVal), vars)

runLivenessAnalysis :: MonadValue -> Bool
runLivenessAnalysis m =  
         if (fst (livenessAnalysis m Map.empty)) == False then
           error ("\n\nInvalid Program. Use of undeclared variable.\n No debug information found.\n")
         else True

isSetNEmpty :: Expr -> Bool
isSetNEmpty (Eset e) = ((DSET.size e) > 0)
isSetNEmpty _ = False

translateExecKuifje :: Stmt -> Map.Map String (Stmt, [String], [Expr]) -> Map.Map String Expr -> MonadValue -> (MonadValue, Map.Map String (Stmt, [String], [Expr]), Map.Map String Expr)
-- Sequence Statements
translateExecKuifje (Seq []) fBody fCntx list = (list, fBody, fCntx)
translateExecKuifje (Seq ls) fBody fCntx list = 
        let (hdRes, hdFBody, hdFCntx) = (translateExecKuifje (head ls) fBody fCntx list)
            (tlRes, tlFBody, tlFCntx) = (translateExecKuifje (Seq (tail ls)) hdFBody hdFCntx hdRes)
         in (translateExecKuifje (Seq (tail ls)) hdFBody hdFCntx hdRes)
-- Assign Statements
translateExecKuifje (Assign id expr) fBody fCntx list = 
        let newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)
-- Support Statements
translateExecKuifje (Support id (Var idexp)) fBody fCntx list = 
        let gammaL = createMonnad list
            kuifje = hysem gammaL (uniform [E.empty])
            executed = exec idexp kuifje
            support = getSupportFromHyper executed
            dist = recoverSupportAsDistList support
         in if ((length dist) == 1)
            then let setExpr = valueToExpr (snd (convertTuple (head dist)))
                     (newRes, newFBody, newFCntx) = translateExecKuifje (Assign id setExpr) fBody fCntx list
                  in (newRes, newFBody, newFCntx)
            else let setExpr = (INUchoices dist)
                     (newRes, newFBody, newFCntx) = translateExecKuifje (Assign id setExpr) fBody fCntx list
                  in (newRes, newFBody, newFCntx)
translateExecKuifje (Support id exp) fBody fCntx list =
        let distName = "DIST." ++ id
            (newRes, newFBody, newFCntx) = translateExecKuifje (Assign distName exp) fBody fCntx list
         in translateExecKuifje (Support id (Var distName)) newFBody newFCntx newRes
-- Function Statements
translateExecKuifje (FuncStmt name body lInput) fBody fCntx list =
        let (Seq insts) = body
            lOutput = findReturns insts
            nMap = Map.insert name (body, lInput, lOutput) fBody
            stmt = fst3 (translateExecKuifje (Kuifje.Syntax.Skip) fBody fCntx list)
            monadList = concatMonadValues list stmt
         in (monadList, nMap, fCntx)
-- Return Statements
--   Returns were processed by FuncStmt, and should be skiped at this point:
translateExecKuifje (ReturnStmt outputs) fBody fCntx list = (list, fBody, fCntx)
-- Call Statements
translateExecKuifje (CallStmt name lInput lOutput) fBody fCntx list =
        let base = (getFuncBody name fBody)
            baseStmt = fst3 base
            fInput = snd3 base
            fOutput = trd3 base
            baseUpdated = updateStmtUses name baseStmt
            outCntxStmt = addOutputCntx name fOutput lOutput baseUpdated
            inCntxStmt = addInputCntx name fInput lInput outCntxStmt
         --in error ("Call is:\n" ++ (show inCntxStmt))
         in translateExecKuifje inCntxStmt fBody fCntx list
-- If statements
translateExecKuifje (Kuifje.Syntax.If e s1 s2) fBody fCntx list =
        let listTrue = (fst3 (translateExecKuifje s1 fBody fCntx (L [])))
            listFalse = (fst3 (translateExecKuifje s2 fBody fCntx (L [])))
            (newRes, newFBody, newFCntx) = ((C e listTrue listFalse), fBody, fCntx)
            monadList = concatMonadValues list newRes
         in (monadList, newFBody, newFCntx)
-- While Statements
translateExecKuifje (Kuifje.Syntax.While e body) fBody fCntx list =
        -- If a variable controls a loop, it is leaked to the adversary:
        let (lBody, newFBody, newFCntx) = translateExecKuifje body fBody fCntx (O e)
            monadList = concatMonadValues list (W e lBody)
         in (monadList, newFBody, newFCntx)
-- For Statements
translateExecKuifje (For var (Var idSet) body) fBody fCntx list =
        -- Check if the set is empty
        let val = getCntxExpr idSet fCntx
         in if (isSetNEmpty val)
            -- Unroll the first element
            then let (Eset elm) = val
                     ls = DSET.elems elm
                     expr = (head ls)
                     newSet = (Eset (DSET.fromList (tail ls)))
                     newFCntx = Map.insert var expr fCntx
                     monadList = concatMonadValues list (A var expr)
                     (lNext, newFBody2, newFCntx2) = translateExecKuifje body fBody newFCntx monadList
                  in translateExecKuifje (For var newSet body) newFBody2 newFCntx2 lNext
            else (translateExecKuifje Kuifje.Syntax.Skip fBody fCntx list)
translateExecKuifje (For var set body) fBody fCntx list =
        -- Check if the set is empty
         if (isSetNEmpty set)
         -- Unroll the first element
         then let (Eset elm) = set
                  ls = DSET.elems elm
                  expr = (head ls)
                  newSet = (Eset (DSET.fromList (tail ls)))
                  newFCntx = Map.insert var expr fCntx
                  monadList = concatMonadValues list (A var expr)
                  --(monadVar, newFBody, newFCntx) = translateExecKuifje (Assign var el) fBody fCntx list
                  (lNext, newFBody2, newFCntx2) = translateExecKuifje body fBody newFCntx monadList
               in translateExecKuifje (For var newSet body) newFBody2 newFCntx2 lNext
         else (translateExecKuifje Kuifje.Syntax.Skip fBody fCntx list)
-- Skip Statements
translateExecKuifje Kuifje.Syntax.Skip fBody fCntx list = ((concatMonadValues list (M skip)), fBody, fCntx)
-- Leak Statements
translateExecKuifje (Leak e) fBody fCntx list = ((concatMonadValues list (O e)), fBody, fCntx)
-- Vis Statements
translateExecKuifje (Vis s) fBody fCntx list = ((concatMonadValues list (M undefined)), fBody, fCntx)
-- External Choice Statements
translateExecKuifje (Echoice s1 s2 p) fBody fCntx list = 
        let listTrue = (fst3 (translateExecKuifje s1 fBody fCntx (L [])))
            listFalse = (fst3 (translateExecKuifje s2 fBody fCntx (L [])))
            (newRes, newFBody, newFCntx) = ((E listTrue listFalse p), fBody, fCntx)
            monadList = concatMonadValues list newRes
         in (monadList, newFBody, newFCntx)
-- Sampling Statements
translateExecKuifje (Sampling id (Var idexp)) fBody fCntx list =
        let exprD = getCntxExpr idexp fCntx
            expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)
translateExecKuifje (Sampling id exprD) fBody fCntx list =
        let expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, fBody, newFCntx)
-- Default Value - Case a Statement is not found
translateExecKuifje stmt _ _ list = error ("Invalid Statement:\n" ++ (show stmt) ++ "\nList:\n" ++ (monadType list))

isReturnStmt :: Stmt -> Bool
isReturnStmt (ReturnStmt _) = True
isReturnStmt _ = False

getReturnExpr :: Stmt -> [Expr]
getReturnExpr (ReturnStmt expr) = expr
getReturnExpr _ = []

findReturns :: [Stmt] -> [Expr]
-- Skip if no returns were found
findReturns [] = []
findReturns fBody = 
           let hd = (head fBody)
               tl = findReturns (tail fBody) 
           in if (isReturnStmt hd)
              then (getReturnExpr hd) ++ tl
              else tl

addInputCntx :: String -> [String] -> [Expr] -> Stmt -> Stmt
addInputCntx fName [] [] stmt = stmt
addInputCntx fName [] _  stmt = error ("Invalid Call to " ++ fName)
addInputCntx fName _  [] stmt = error ("Invalid Call to " ++ fName)
addInputCntx fName fInputs cInputs stmt = 
        let id = (fName ++ "." ++ (head fInputs))
            expr = (head cInputs)
            nAssngStmt = (Assign id expr)
            nStmt = (appendStmtBegin nAssngStmt stmt)
        in (addInputCntx fName (tail fInputs) (tail cInputs) nStmt)

addOutputCntx :: String -> [Expr] -> [String] -> Stmt -> Stmt
addOutputCntx fName [] [] stmt = stmt
addOutputCntx fName [] _  stmt = error ("Invalid Call to " ++ fName)
addOutputCntx fName _  [] stmt = error ("Invalid Call to " ++ fName)
addOutputCntx fName fOutputs cOutputs stmt =
        let id = (head cOutputs)
            expr = (updateVarToCntx fName (head fOutputs))
            nAssngStmt = (Assign id expr)
            nStmt = (appendStmtEnd nAssngStmt stmt)
        in (addOutputCntx fName (tail fOutputs) (tail cOutputs) nStmt)

appendStmtBegin :: Stmt -> Stmt -> Stmt
appendStmtBegin st1 (Seq ls) = (Seq (st1 : ls))
appendStmtBegin st1 stmt = (Seq [st1, stmt])

appendStmtEnd :: Stmt -> Stmt -> Stmt
appendStmtEnd st1 (Seq ls) = (Seq (ls ++ [st1]))
appendStmtEnd st1 stmt = (Seq [stmt, st1])

updateVarToCntx :: String -> Expr -> Expr
updateVarToCntx fName (Var id) = (Var (fName ++ "." ++ id))
-- (addOutputCntx fName (tail fOutputs) (tail cOutputs) nStmt)

updateID :: String -> Stmt -> Stmt
updateID fName (Assign id expr) = (Assign (fName ++ "." ++ id) expr)
updateID fName (Sampling id expr) = (Sampling (fName ++ "." ++ id) expr)
updateID fName (Support id expr) = (Support (fName ++ "." ++ id) expr)
updateID fName e = e

updateExpression :: String -> Expr -> Expr
updateExpression fName (Var id) = (Var (fName ++ "." ++ id))
updateExpression fName (Neg r) =
     let newr = (updateExpression fName r)
     in (Neg newr)
updateExpression fName (ExprIf cond e1 e2) =
     let newcond = (updateExpression fName cond)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (ExprIf newcond newe1 newe2)
updateExpression fName (ABinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (ABinary op newe1 newe2)
updateExpression fName (Ichoice e1 e2 p) =
     let newp = (updateExpression fName p)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (Ichoice newe1 newe2 newp)
updateExpression fName (Ichoices []) = (Ichoices [])
updateExpression fName (Ichoices ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (Ichoices (tail ls)))
         (Ichoices list) = tl
     in (Ichoices (hd : list))
updateExpression fName (IchoiceDist e1 e2 p) =
     let newp = (updateExpression fName p)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (IchoiceDist newe1 newe2 newp)
updateExpression fName (IchoicesDist []) = (Ichoices [])
updateExpression fName (IchoicesDist ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (Ichoices (tail ls)))
         (IchoicesDist list) = tl
     in (IchoicesDist (hd : list))
updateExpression fName (Tuple e p) =
     let newe = (updateExpression fName e)
     in (Tuple newe p)
updateExpression fName (INUchoices []) = (INUchoices [])
updateExpression fName (INUchoices ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (INUchoices (tail ls)))
         (INUchoices list) = tl
     in (INUchoices (hd : list))
updateExpression fName (BBinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (BBinary op newe1 newe2)
updateExpression fName (RBinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (RBinary op newe1 newe2)
-- Support to Set not provided.
updateExpression fName e = e
updateStmtList :: String -> [Stmt] -> [Stmt]
updateStmtList fName [] = []
updateStmtList fName ls = (updateStmtUses fName (head ls)) : (updateStmtList fName (tail ls))

updateStmtUses :: String -> Stmt -> Stmt
updateStmtUses fName (Seq []) = (Seq [])
updateStmtUses fName (Seq ls) =
     let hd = (updateStmtUses fName (head ls))
         tl = (updateStmtUses fName (Seq (tail ls)))
         (Seq list) = tl
     in (Seq (hd : list))
updateStmtUses fName (Assign id expr) = 
     let newexpr = (updateExpression fName expr)
     in (updateID fName (Assign id newexpr))
updateStmtUses fName (Kuifje.Syntax.While e s) = 
     (Kuifje.Syntax.While (updateExpression fName e) (updateStmtUses fName s)) 
updateStmtUses fName (Kuifje.Syntax.If e s1 s2) =
     (Kuifje.Syntax.If (updateExpression fName e) (updateStmtUses fName s1) (updateStmtUses fName s2))
updateStmtUses fName (Leak e) = (Leak (updateExpression fName e))
updateStmtUses fName (Echoice s1 s2 p) =
     (Echoice (updateStmtUses fName s1) (updateStmtUses fName s2) (updateExpression fName p))
updateStmtUses fName (Sampling id expr) =
     let newexpr = (updateExpression fName expr)
     in (updateID fName (Sampling id newexpr))
updateStmtUses fName (Support id expr) =       
     let newexpr = (updateExpression fName expr)
     in (updateID fName (Support id newexpr))
updateStmtUses fName stmt = stmt

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

trd3 :: (a, b, c) -> c
trd3 (_, _, x) = x

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

snd4 :: (a, b, c, d) -> b
snd4 (_, x, _, _) = x

trd4 :: (a, b, c, d) -> c
trd4 (_, _, x, _) = x

frt4 :: (a, b, c, d) -> d
frt4 (_, _, _, x) = x

fromJust :: Maybe (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
fromJust (Just a) = a
fromJust Nothing = error "Function not found."

getFuncBody :: String -> Map.Map String (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
getFuncBody id funcBody = fromJust (Map.lookup id funcBody)

--evalCaseStmt :: Stmt -> Expr
--evalCaseStmt (CaseStmt exp stmt) = exp

getRational :: Gamma -> String -> Rational
getRational g s | Just (R t) <- E.lookup g s = t
                | otherwise = error ("Not going to happen " ++ s)

project :: Dist (Dist Gamma) -> Dist (Dist Rational)
project = fmap (fmap (\s -> getRational s "y"))

initGamma :: Rational -> Rational -> Gamma
initGamma x y = let g = E.add E.empty ("x", (R x)) in 
               E.add g ("y", (R y))

hyper :: Dist (Dist Rational)
hyper = let g = createMonnad (fst3 (translateExecKuifje exampelS Map.empty Map.empty (L [])))
         in project $ hysem g (uniform [E.empty])

example :: String
example = "y := 0; while (x > 0) do y := x + y; x := x - 1; od;"

exampelS :: Stmt
exampelS = let (Seq ls) = parseString example 
            in Seq $ (Assign "x" (Ichoice
                        (RationalConst (5 % 1)) 
                        (RationalConst (6 % 1)) 
                        (RationalConst (1 % 2)) )):ls
