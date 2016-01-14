{-# OPTIONS -Wall #-}







-- | This module defines equality on LC terms. Since this variant doesn't use
-- unification, all that's necessary is simple equality.

module Simple.Monadic.Equality where

import Simple.Core.Type

import Data.Functor.Classes







instance Eq1 TypeF where
  eq1 (TyCon c) (TyCon c') =
    c == c'
  eq1 (Fun a b) (Fun a' b') =
    a == a' && b == b'
  eq1 _ _ = False