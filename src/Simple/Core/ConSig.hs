{-# OPTIONS -Wall #-}







-- | This module implements constructor signatures, for data declarations.

module Simple.Core.ConSig where

import Utils.Pretty (pretty)
import Simple.Core.Type

import Data.List (intercalate)







-- | A constructor signature in this variant is simply a list of argument
-- types and a return type.

data ConSig = ConSig [Type] Type


instance Show ConSig where
  show (ConSig as r) =
    "(" ++ intercalate "," (map pretty as) ++ ")" ++ pretty r