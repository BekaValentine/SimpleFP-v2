{-# OPTIONS -Wall #-}







-- | This module defines equality on dependently typed LC terms. Since this
-- variant doesn't use unification, all that's necessary is simple equality.

module Dependent.Monadic.Equality where

import Dependent.Core.Term

import Data.Functor.Classes

import Utils.ABT






instance Eq1 TermF where
  liftEq eq (Defined n) (Defined n') =
    n == n'
  liftEq eq (Ann m t) (Ann m' t') =
    eq m m' && eq t t'
  liftEq eq Type Type = True
  liftEq eq (Fun arg sc) (Fun arg' sc') =
    eq arg arg' && eq sc sc'
  liftEq eq (Lam sc) (Lam sc') =
    eq sc sc'
  liftEq eq (App f x) (App f' x') =
    eq f f' && eq x x'
  liftEq eq (Con c as) (Con c' as') =
    c == c' && liftEq eq as as'
  liftEq eq (Case as mot cls) (Case as' mot' cls') =
    liftEq eq as as' && liftEq eq mot mot' &&
      length cls == length cls' && and (zipWith (liftEq eq) cls cls')
  liftEq _ _ _ = False


instance Eq1 CaseMotiveF where
  liftEq eq (CaseMotive t) (CaseMotive t') = liftEq eq t t'


instance Eq1 ClauseF where
  liftEq eq (Clause pscs bsc) (Clause pscs' bsc') =
    length pscs == length pscs' && and (zipWith (liftEq eq) pscs pscs') &&
      eq bsc bsc'


instance Eq1 PatternF where
  liftEq eq (PatternF x) (PatternF x') = eqScopes eq x x'
    where
      eqScopes :: (a -> b -> Bool) -> Scope (PatternFF a) -> Scope (PatternFF b) -> Bool
      eqScopes eq' = liftScopeEq (liftABTEq $ liftEq2 eq' (eqScopes eq'))


instance Eq a => Eq1 (PatternFF a) where
  liftEq eq (ConPat c ps) (ConPat c' ps') =
    c == c' && liftEq eq ps ps'
  liftEq eq (AssertionPat m) (AssertionPat m') =
    m == m'
  liftEq _ _ _ = False

instance Eq2 PatternFF where
  liftEq2 eq eq' (ConPat c ps) (ConPat c' ps') =
    c == c' && liftEq eq' ps ps'
  liftEq2 eq eq' (AssertionPat m) (AssertionPat m') =
    eq m m'
  liftEq2 _ _ _ _ =
    False
