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





-- | A signature is a collection of type constructors, and data constructors
-- together with their constructor signatures. This is used during type
-- checking and elaboration to define the underlying type theory.

data Signature = Signature [String] [(String,ConSig)]


instance Show Signature where
  show (Signature tycons consigs) =
    "Types: " ++ unwords tycons ++ "\n" ++
    "Constructors:\n" ++
      unlines [ "  " ++ c ++ "(" ++
                intercalate "," (map pretty args) ++
                ") : " ++ pretty ret
              | (c, ConSig args ret) <- consigs
              ]