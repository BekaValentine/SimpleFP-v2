{-# OPTIONS -Wall #-}







-- | This module defines equality on dependently typed LC terms. Since this
-- variant doesn't use unification, all that's necessary is simple equality.

module Dependent.Monadic.Equality where

import Dependent.Core.Term

import Data.Functor.Classes







instance Eq1 TermF where
  eq1 (Defined n) (Defined n') =
    n == n'
  eq1 (Ann m t) (Ann m' t') =
    m == m' && t == t'
  eq1 Type Type = True
  eq1 (Fun arg sc) (Fun arg' sc') =
    arg == arg' && sc == sc'
  eq1 (Lam sc) (Lam sc') =
    sc == sc'
  eq1 (App f x) (App f' x') =
    f == f' && x == x'
  eq1 (Con c as) (Con c' as') =
    c == c' && as == as'
  eq1 (Case as mot cls) (Case as' mot' cls') =
    as == as' && eq1 mot mot' &&
      length cls == length cls' && and (zipWith eq1 cls cls')
  eq1 _ _ = False


instance Eq1 CaseMotiveF where
  eq1 (CaseMotive t) (CaseMotive t') = eq1 t t'


instance Eq1 ClauseF where
  eq1 (Clause pscs bsc) (Clause pscs' bsc') =
    length pscs == length pscs' && and (zipWith eq1 pscs pscs') &&
      bsc == bsc'


instance Eq1 PatternF where
  eq1 (PatternF x) (PatternF y) = x == y


instance Eq a => Eq1 (PatternFF a) where
  eq1 (ConPat c ps) (ConPat c' ps') =
    c == c' && ps == ps'
  eq1 (AssertionPat m) (AssertionPat m') =
    m == m'
  eq1 _ _ = False