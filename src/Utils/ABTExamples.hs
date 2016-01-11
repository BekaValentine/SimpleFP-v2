{-# OPTIONS -Wall #-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}





module Utils.ABTExamples where

import Utils.ABT





-- | A simple example LC type for testing the functionality of ABTs.

data LC r
  = Defined String
  | Pair r r | Fst r | Snd r
  | Lam r | App r r
  deriving (Show,Functor,Foldable)

pairH x y = In (Pair (scope [] x) (scope [] y))
fstH p = In (Fst (scope [] p))
sndH p = In (Snd (scope [] p))
lamH n b = In (Lam (scope [n] b))
appH f x = In (App (scope [] f) (scope [] x))

ex :: ABT LC
ex = lamH "p" (pairH (sndH (Var (Free "p"))) (fstH (Var (Free "foo"))))