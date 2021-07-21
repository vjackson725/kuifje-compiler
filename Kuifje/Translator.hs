{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Translator where 

import qualified Kuifje.Env as E
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
                          otherwise -> error "Variable not in scope"
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
evalE (INUchoices ls) = 
  if length ls == 1
     then evalE $ head ls
     else \s ->
        let e1' = (evalE $ head ls) s
            e2' = (evalE $ INUchoices (tail ls)) s
         in D $ unionWith (+) (runD e1') (runD e2')
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

translateKuifje :: Stmt -> Kuifje Gamma 
translateKuifje (Seq []) = skip
translateKuifje (Seq ls) = translateKuifje (head ls) <> translateKuifje (Seq (tail ls))
translateKuifje (Assign id expr) = Language.Kuifje.Syntax.update (\s -> 
        let currS = (evalE expr) s in
            fmap (\r -> E.add s (id, r)) currS)
translateKuifje (Kuifje.Syntax.While e s) = 
        Language.Kuifje.Syntax.while (\s -> 
                let currS = (evalE e) s in 
                    fmap (\r -> case r of (B b) -> b) currS) (translateKuifje s)
translateKuifje (Kuifje.Syntax.If e s1 s2) = 
        Language.Kuifje.Syntax.cond 
          (\s -> let currS = (evalE e) s in fmap (\r -> case r of (B b) -> b) currS) 
          (translateKuifje s1) 
          (translateKuifje s2)
translateKuifje Kuifje.Syntax.Skip = skip
translateKuifje (Leak e) = observe (evalE e)
translateKuifje (Vis s) = undefined
translateKuifje (Echoice s1 s2 p) = 
        Language.Kuifje.Syntax.cond 
          (\s -> let p' = (evalE (Ichoice (BoolConst True) (BoolConst False) p) s) 
                  in (fmap (\r -> case r of (B b) -> b)) p') 
          (translateKuifje s1) 
          (translateKuifje s2)

getRational :: Gamma -> String -> Rational
getRational g s | Just (R t) <- E.lookup g s = t
                | otherwise = error ("Not going to happen " ++ s)

project :: Dist (Dist Gamma) -> Dist (Dist Rational)
project = fmap (fmap (\s -> getRational s "y"))

initGamma :: Rational -> Rational -> Gamma
initGamma x y = let g = E.add E.empty ("x", (R x)) in 
               E.add g ("y", (R y))

hyper :: Dist (Dist Rational)
hyper = let g = translateKuifje exampelS 
         in project $ hysem g (uniform [E.empty])

example :: String
example = "y := 0; while (x > 0) do y := x + y; x := x - 1; od;"

exampelS :: Stmt
exampelS = let (Seq ls) = parseString example 
            in Seq $ (Assign "x" (Ichoice
                        (RationalConst (5 % 1)) 
                        (RationalConst (6 % 1)) 
                        (RationalConst (1 % 2)) )):ls
