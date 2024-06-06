{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.PrettyPrint where

import Kuifje.Value

import Text.PrettyPrint.Boxes
import qualified Data.Set as S
import qualified Data.Map as M
import Numeric
import Language.Kuifje.PrettyPrint
import Language.Kuifje.Distribution

import Prelude hiding ((<>))

import Kuifje.Env

instance Boxable (Value) where
  toBox (R x) = text "R" <+> text (show $ fromRat x)
  toBox (T x) = text "T" <+> text (show $ x)
  toBox (B x) = text "B" <+> text (show x)
  toBox (S x) = text "S" <+> (toBox $ S.elems x)
  toBox (PD x) = text "PD" <+> (toBox $ S.elems x)
  toBox (LS x) = text "LS" <+> (toBox $ x)
  toBox (TP x) = text "TP" <+> text (valueToString (TP x))

instance Boxable (Env Value) where
  toBox (Env m) =
    text "{"
      <+> punctuateH left (text ", ")
        (map
          (\(x,v) -> text x <> text ":" <+> toBox v)
          (M.assocs m))
      <+> text "}"

instance (Boxable a, Boxable b) => Boxable (Either a b) where
  toBox (Left x) = text "Left" <+> toBox x
  toBox (Right x) = text "Right" <+> toBox x
