{-# OPTIONS -Wall #-}







-- | This module defines equality on LC terms. Since this variant doesn't use
-- unification, all that's necessary is simple equality.

module Simple.Monadic.Equality where

import Simple.Core.Type

import Data.Functor.Classes







instance Eq1 TypeF where
  liftEq _ (TyCon c) (TyCon c') =
    c == c'
  liftEq eq (Fun a b) (Fun a' b') =
    eq a a' && eq b b'
  liftEq _ _ _ = False
