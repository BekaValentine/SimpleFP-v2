{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}







-- | This module defines unification of dependent types.

module Dependent.Unification.Unification where

import Utils.ABT
import Utils.Elaborator
import Utils.Pretty
import Utils.Telescope
import Utils.Unifier
import Dependent.Core.Term
import Dependent.Unification.Elaborator

import Control.Monad.Except







-- | Equating terms by trivial structural equations.

instance MonadUnify TermF Elaborator where
  equate (Defined n1) (Defined n2) =
    if n1 == n2
       then return []
       else throwError $ "Mismatching names " ++ n1 ++ " and " ++ n2
  equate (Ann m1 t1) (Ann m2 t2) =
    return [ Equation (instantiate0 m1) (instantiate0 m2)
           , Equation (instantiate0 t1) (instantiate0 t2)
           ]
  equate Type Type =
    return []
  equate (Fun a1 sc1) (Fun a2 sc2) =
    do ns <- freshRelTo (names sc1) context
       let xs = map (Var . Free) ns
       return [ Equation (instantiate0 a1) (instantiate0 a2)
              , Equation (instantiate sc1 xs) (instantiate sc2 xs)
              ]
  equate (Lam sc1) (Lam sc2) =
    do ns <- freshRelTo (names sc1) context
       let xs = map (Var . Free) ns
       return [ Equation (instantiate sc1 xs) (instantiate sc2 xs) ]
  equate (App f1 a1) (App f2 a2) =
    return [ Equation (instantiate0 f1) (instantiate0 f2)
           , Equation (instantiate0 a1) (instantiate0 a2)
           ]
  equate (Con c1 as1) (Con c2 as2) =
    do unless (c1 == c2)
         $ throwError $ "Mismatching constructors "
                     ++ c1 ++ " and " ++ c2
       unless (length as1 == length as2)
         $ throwError $ "Mismatching constructor arg lengths between "
                         ++ pretty (In (Con c1 as1)) ++ " and "
                         ++ pretty (In (Con c2 as1))
       return $ zipWith
                  Equation
                  (map instantiate0 as1)
                  (map instantiate0 as2)
  equate (Case as1 mot1 cs1) (Case as2 mot2 cs2) =
    do unless (length as1 == length as2)
         $ throwError $ "Mismatching number of case arguments in "
                     ++ pretty (In (Case as1 mot1 cs1)) ++ " and "
                     ++ pretty (In (Case as2 mot2 cs2))
       unless (length cs1 == length cs2)
         $ throwError $ "Mismatching number of clauses in "
                     ++ pretty (In (Case as1 mot1 cs1)) ++ " and "
                     ++ pretty (In (Case as2 mot2 cs2))
       let argEqs = zipWith
                      Equation
                        (map instantiate0 as1)
                        (map instantiate0 as2)
       motEqs <- equateCaseMotive mot1 mot2
       clauseEqs <- fmap concat $ zipWithM equateClause cs1 cs2
       return $ argEqs ++ motEqs ++ clauseEqs
  equate l r =
    throwError $ "Cannot unify " ++ pretty (In l) ++ " with " ++ pretty (In r)





-- | Equating case motives as a special helper for the main 'equate' method.

equateCaseMotive :: CaseMotive -> CaseMotive -> Elaborator [Equation Term]
equateCaseMotive mot1@(CaseMotive tele1) mot2@(CaseMotive tele2) =
  do ns <- freshRelTo (namesTelescope tele1) context
     let xs = map (Var . Free) ns
     let (as1, b1) = instantiateTelescope tele1 xs
         (as2, b2) = instantiateTelescope tele2 xs
     unless (length as1 == length as2)
       $ throwError $ "Motives not equal: " ++ pretty mot1 ++ " and "
                   ++ pretty mot2
     return $ zipWith Equation as1 as2 ++ [ Equation b1 b2 ]
     




-- Equating clauses as a special helper for the main 'equate' method.

equateClause :: Clause -> Clause -> Elaborator [Equation Term]
equateClause (Clause pscs1 sc1) (Clause pscs2 sc2) =
  do unless (length pscs1 == length pscs2)
       $ throwError "Clauses have different numbers of patterns."
     unless (length (names sc1) == length (names sc2))
       $ throwError "Patterns bind different numbers of arguments."
     ns <- freshRelTo (names sc1) context
     let xs = map (Var . Free) ns
         xs' = map (Var . Free) ns
         ps1 = map (\sc -> patternInstantiate sc xs xs') pscs1
         ps2 = map (\sc -> patternInstantiate sc xs xs') pscs2
         b1 = instantiate sc1 xs'
         b2 = instantiate sc2 xs'
     case sequence (zipWith zipABTF ps1 ps2) of
       Nothing ->
         throwError "Patterns are not equal."
       Just pEqss ->
         return $ [ Equation a1 a2 | (a1,a2) <- concat pEqss ]
               ++ [ Equation b1 b2 ]