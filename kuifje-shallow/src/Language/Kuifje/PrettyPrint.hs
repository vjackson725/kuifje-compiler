{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Language.Kuifje.PrettyPrint where

import Data.List (transpose, intersperse)
import qualified Text.PrettyPrint.Boxes as PP
import qualified Data.Map.Strict as HM

import Debug.Trace

import Language.Kuifje.Distribution

import Numeric

class Boxable a where
  toBox :: a -> PP.Box


instance Boxable Bool where
  toBox = PP.text . show

instance Boxable Integer where
  toBox = PP.text . show

instance Boxable Int where
  toBox = PP.text . show

instance Boxable Rational where
  toBox = PP.text . show . fromRat

instance Boxable a => Boxable [a] where
  toBox xs =
    let vs = map toBox xs
    in PP.text "[" PP.<+>
       boxmiddle vs PP.<+>
       PP.text "]"
    where
      boxmiddle ([b]) = b
      boxmiddle (b : bs) = b PP.<> PP.text "," PP.<+> boxmiddle bs
      boxmiddle [] = PP.text ""

instance (Show a, Show b) => Boxable (a,b) where
  toBox = PP.text . show

instance (Show a, Show b, Show c) => Boxable (a,b,c) where
  toBox = PP.text . show

instance (Show a, Show b, Show c, Show d) => Boxable (a,b,c,d) where
  toBox = PP.text . show

distToBox :: (Ord a, Boxable a) => Dist a -> PP.Box
distToBox =
  tabulate . map (\(a,b) -> [toBox b, toBox a]) . HM.toList . unpackD

instance (Boxable a, Ord a) => Boxable (Dist a) where
  toBox = distToBox

tabulate :: [[PP.Box]] -> PP.Box
tabulate rs = table
  where
   heights  = map (maximum . map PP.rows) rs
   rs''     = zipWith (\r h -> map (PP.alignVert PP.top h) r) rs heights
   columns  = transpose rs''
   widths   = map (maximum . map PP.cols) columns
   rs'      = transpose $ zipWith (\c w -> map (PP.alignHoriz PP.left w) c) columns widths
   columns' = map (PP.hsep 3 PP.top) rs'
   table    = PP.vsep 0 PP.left columns'
