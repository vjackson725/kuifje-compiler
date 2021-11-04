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
import Kuifje.PrettyPrint 
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Control.Applicative

import System.IO 
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

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
          
aOperatorWarpper op (S x) (S y) = 
        case op of 
          Add      -> S $ DSET.union x y
          Subtract -> S $ x DSET.\\ y
          otherwise -> error "Unknow set operation"

aOperator op d1 d2 = 
  D $ fromListWith (+) [((aOperatorWarpper op x y), p * q) | (x, p) <- toList $ runD d1,
                                                             (y, q) <- toList $ runD d2]
cOperator op d1 d2 = 
  D $ fromListWith (+) [((B (op x y)), p * q) | (R x, p) <- toList $ runD d1,
                                                (R y, q) <- toList $ runD d2]
bOperator op d1 d2 = 
  D $ fromListWith (+) [((B (op x y)), p * q) | (B x, p) <- toList $ runD d1,
                                                (B y, q) <- toList $ runD d2]

evalE :: Expr -> (Gamma ~> Value)
evalE (Var id) = \s -> case E.lookup s id of 
                          Just v -> (return v)
                          otherwise -> error ("Variable " ++ id ++ " not in scope")
evalE (RationalConst r) = \s -> return (R r)
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
evalE (Ichoices ls) = 
   if length ls == 1 
      then evalE $ head ls
      else evalE $ Ichoice 
                          (head ls) 
                          (Ichoices (tail ls)) 
                          (RationalConst (1 % (toInteger (length ls))))
evalE (Tuple e p) = \s ->
  let e' = (evalE e) s
      p' = Data.List.foldr (\x y -> case x of (R x', q) -> x'*q*y) 1
              $ toList $ runD $ (evalE p) s
      d = D $ Data.Map.Strict.map (*p') $ runD e'
   in D $ (runD d)
--evalTList (Tuple _ p) = p
--evalTList (INUchoices ls) =
--  if length ls == 1
--     then evalTList $ head ls
--     else \s ->
--        let e1' = (evalTList $ head ls) s
--            e2' = (evalE $ INUchoices (tail ls)) s
--         in e1' + e2'
evalE (INUchoices ls) =
  if (evalTList $ INUchoices ls) == 1.0
     then evalNUList $ INUchoices ls
     else error ("Probability adds up to: " ++ 
          (show (evalTList $ INUchoices ls)) ++
          " --> It should be 1.0" )

--evalE (INUchoices ls) =
--  if length ls == 1
--     then evalE $ head ls
--     else \s ->
--        let e1' = (evalE $ head ls) s
--            e2' = (evalE $ INUchoices (tail ls)) s
--         in D $ unionWith (+) (runD e1') (runD e2')
evalE (BoolConst b) = \s -> return (B b)
evalE (Not b) = \s -> 
        let r' = (evalE b) s 
         in (fmap (\bv -> case bv of 
                            (B b') -> B (not b'))) r'
evalE (BBinary op e1 e2) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s in 
      case op of 
        And -> (bOperator (&&) e1' e2') -- /\
        Or  -> (bOperator (||) e1' e2') -- \/
evalE (RBinary op e1 e2) = \s -> 
  let e1' = (evalE e1) s
      e2' = (evalE e2) s in 
      case op of 
        Gt -> (cOperator (>) e1' e2')
        Ge -> (cOperator (>=) e1' e2')
        Lt -> (cOperator (<) e1' e2')
        Le -> (cOperator (<=) e1' e2')
        Eq -> (cOperator (==) e1' e2')
        Ne -> (cOperator (/=) e1' e2')
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
evalE (ExprSwitch var ls def) = 
  if length ls == 0
      then evalE $ def
      else \s ->
         let val = head (evalCase (head ls))
             e1 = head (tail (evalCase (head ls)))
             cond = ((RBinary Eq) var val)
             cond' = runD $ (evalE cond) s
             e1' = (evalE e1) s
             e2' = (evalE $ ExprSwitch var (tail ls) def) s
             d1 = case Data.Map.Strict.lookup (B True) cond' of
                    (Just p)  -> D $ Data.Map.Strict.map (*p) $ runD e1'
                    otherwise -> D $ Data.Map.Strict.empty
             d2 = case Data.Map.Strict.lookup (B False) cond' of
                    (Just p)  -> D $ Data.Map.Strict.map (*p) $ runD e2'
                    otherwise -> D $ Data.Map.Strict.empty
             in D $ unionWith (+) (runD d1) (runD d2)
evalE (Case val e) =
  evalE $ e

evalCase :: Expr -> [Expr]
evalCase (Case val e) = 
  [val, e]

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
--error ("Value is " ++ (show p))
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

evalNUList (INUchoices ls) =
  if length ls == 1
     then evalE $ head ls
     else \s ->
        let e1' = (evalE $ head ls) s
            e2' = (evalNUList $ INUchoices (tail ls)) s
         in D $ unionWith (+) (runD e1') (runD e2')


translateKuifje :: Stmt -> Map.Map String (Stmt, [String], [Expr]) -> (Kuifje Gamma, Map.Map String (Stmt, [String], [Expr]) )
translateKuifje (Seq []) fBody = (skip, fBody)
translateKuifje (Seq ls) fBody = 
        let (hdRes, newFBody) = (translateKuifje (head ls) fBody)
        in (hdRes, newFBody) <> translateKuifje (Seq (tail ls)) newFBody
translateKuifje (Assign id expr) fBody = (Language.Kuifje.Syntax.update (\s ->
        let currS = (evalE expr) s in
            fmap (\r -> E.add s (id, r)) currS), fBody)
translateKuifje (Kuifje.Syntax.While e s) fBody = 
        (Language.Kuifje.Syntax.while (\s -> 
                let currS = (evalE e) s in 
                    fmap (\r -> case r of (B b) -> b) currS) (fst (translateKuifje s fBody)), fBody)
translateKuifje (Kuifje.Syntax.If e s1 s2) fBody = 
        (Language.Kuifje.Syntax.cond 
          (\s -> let currS = (evalE e) s in fmap (\r -> case r of (B b) -> b) currS) 
          (fst (translateKuifje s1 fBody)) 
          (fst (translateKuifje s2 fBody)), fBody)
translateKuifje Kuifje.Syntax.Skip fBody = (skip, fBody)
translateKuifje (Leak e) fBody = (observe (evalE e), fBody)
translateKuifje (Vis s) fBody = (undefined, fBody)
translateKuifje (Echoice s1 s2 p) fBody = 
         (Language.Kuifje.Syntax.cond 
          (\s -> let p' = (evalE (Ichoice (BoolConst True) (BoolConst False) p) s) 
                  in (fmap (\r -> case r of (B b) -> b)) p') 
          (fst (translateKuifje s1  fBody)) 
          (fst (translateKuifje s2 fBody)), fBody)
translateKuifje (CaseStmt exp stmt) fBody =
          translateKuifje stmt fBody
translateKuifje (Switch var list def) fBody =
        if length list == 0
        then (translateKuifje def fBody)
        else (Language.Kuifje.Syntax.cond
          (\s -> let currS = (evalE ((RBinary Eq) var (evalCaseStmt (head list)))) s in fmap (\r -> case r of (B b) -> b) currS)
          (fst (translateKuifje (head list) fBody))
          (fst (translateKuifje (Switch var (tail list) def) fBody)), fBody)
translateKuifje (FuncStmt name body lInput) fBody = 
          let (Seq ls) = body
              lOutput = findReturns ls
              nMap = Map.insert name (body, lInput, lOutput) fBody 
              stmt = fst (translateKuifje (Kuifje.Syntax.Skip) fBody)
          in (stmt, nMap)
-- Returns were processed by FuncStmt, and should be skiped at this point:
translateKuifje (ReturnStmt outputs) fBody = (skip, fBody)
translateKuifje (CallStmt name lInput lOutput) fBody =
          let base = (getFuncBody name fBody)
              baseStmt = fst3 base
              fInput = snd3 base
              fOutput = trd3 base
              baseUpdated = updateStmtUses name baseStmt
              outCntxStmt = addOutputCntx name fOutput lOutput baseUpdated
              inCntxStmt = addInputCntx name fInput lInput outCntxStmt
          in translateKuifje inCntxStmt fBody

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

updateAssingment :: String -> Stmt -> Stmt
updateAssingment fName (Assign id expr) = (Assign (fName ++ "." ++ id) expr)
updateAssingment fName e = e

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
updateExpression fName (ExprSwitch var [] def) =
     let newvar = (updateExpression fName var)
     in (ExprSwitch newvar [] def)
updateExpression fName (ExprSwitch var ls def) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (ExprSwitch var (tail ls) def))
         (ExprSwitch newvar list newdef) = tl
     in (ExprSwitch newvar (hd : list) newdef)
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
     in (updateAssingment fName (Assign id newexpr))
updateStmtUses fName (Kuifje.Syntax.While e s) = 
     (Kuifje.Syntax.While (updateExpression fName e) (updateStmtUses fName s)) 
updateStmtUses fName (Kuifje.Syntax.If e s1 s2) =
     (Kuifje.Syntax.If (updateExpression fName e) (updateStmtUses fName s1) (updateStmtUses fName s2))
updateStmtUses fName (Leak e) = (Leak (updateExpression fName e))
updateStmtUses fName (Echoice s1 s2 p) =
     (Echoice (updateStmtUses fName s1) (updateStmtUses fName s2) (updateExpression fName p))
updateStmtUses fName (CaseStmt exp stmt) =
     (CaseStmt (updateExpression fName exp) (updateStmtUses fName stmt))
updateStmtUses fName (Switch var [] def) =
     (Switch (updateExpression fName var) [] (updateStmtUses fName def)) 
updateStmtUses fName (Switch var ls def) =
     let newVar = (updateExpression fName var)
         newDef = (updateStmtUses fName  def)
         newLs = (updateStmtList fName ls)
     in (Switch newVar newLs newDef)
updateStmtUses fName stmt = stmt

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

trd3 :: (a, b, c) -> c
trd3 (_, _, x) = x

fromJust :: Maybe (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
fromJust (Just a) = a
fromJust Nothing = error "Function not found."

getFuncBody :: String -> Map.Map String (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
getFuncBody id funcBody = fromJust (Map.lookup id funcBody)

evalCaseStmt :: Stmt -> Expr
evalCaseStmt (CaseStmt exp stmt) = exp

getRational :: Gamma -> String -> Rational
getRational g s | Just (R t) <- E.lookup g s = t
                | otherwise = error ("Not going to happen " ++ s)

project :: Dist (Dist Gamma) -> Dist (Dist Rational)
project = fmap (fmap (\s -> getRational s "y"))

initGamma :: Rational -> Rational -> Gamma
initGamma x y = let g = E.add E.empty ("x", (R x)) in 
               E.add g ("y", (R y))

hyper :: Dist (Dist Rational)
hyper = let g = fst (translateKuifje exampelS Map.empty)
         in project $ hysem g (uniform [E.empty])

example :: String
example = "y := 0; while (x > 0) do y := x + y; x := x - 1; od;"

exampelS :: Stmt
exampelS = let (Seq ls) = parseString example 
            in Seq $ (Assign "x" (Ichoice
                        (RationalConst (5 % 1)) 
                        (RationalConst (6 % 1)) 
                        (RationalConst (1 % 2)) )):ls
