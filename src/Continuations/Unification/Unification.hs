{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}







-- | This module defines unification of dependent types.

module Continuations.Unification.Unification where

import Utils.ABT
import Utils.Elaborator
import Utils.Names
import Utils.Pretty
import Utils.Telescope
import Utils.Unifier
import Continuations.Core.Term
import Continuations.Unification.Elaborator

import Control.Monad.Except







-- | Equating terms by trivial structural equations.

instance MonadUnify TermF Elaborator where
  equate (Defined n1) (Defined n2) =
    if n1 == n2
       then return []
       else throwError $ "Mismatching names "
                         ++ showName n1 ++ " and " ++ showName n2
  equate (Ann m1 t1) (Ann m2 t2) =
    return [ Equation (instantiate0 m1) (instantiate0 m2)
           , Equation (instantiate0 t1) (instantiate0 t2)
           ]
  equate Type Type =
    return []
  equate (Fun plic1 a1 sc1) (Fun plic2 a2 sc2) =
    do unless (plic1 == plic2)
         $ throwError $ "Mismatching plicities when unifying "
             ++ pretty (In (Fun plic1 a1 sc1)) ++ " with "
             ++ pretty (In (Fun plic2 a2 sc2))
       ns <- freshRelTo (names sc1) context
       let xs = map (Var . Free) ns
       return [ Equation (instantiate0 a1) (instantiate0 a2)
              , Equation (instantiate sc1 xs) (instantiate sc2 xs)
              ]
  equate (Lam plic1 sc1) (Lam plic2 sc2) =
    do unless (plic1 == plic2)
         $ throwError $ "Mismatching plicities when unifying "
             ++ pretty (In (Lam plic1 sc1)) ++ " with "
             ++ pretty (In (Lam plic2 sc2))
       ns <- freshRelTo (names sc1) context
       let xs = map (Var . Free) ns
       return [ Equation (instantiate sc1 xs) (instantiate sc2 xs) ]
  equate (App plic1 f1 a1) (App plic2 f2 a2) =
    do unless (plic1 == plic2)
         $ throwError $ "Mismatching plicities when unifying "
             ++ pretty (In (App plic1 f1 a1)) ++ " with "
             ++ pretty (In (App plic2 f2 a2))
       return [ Equation (instantiate0 f1) (instantiate0 f2)
              , Equation (instantiate0 a1) (instantiate0 a2)
              ]
  equate (Con c1 as1) (Con c2 as2) =
    do unless (c1 == c2)
         $ throwError $ "Mismatching constructors "
                     ++ showName c1 ++ " and " ++ showName c2
       unless (length as1 == length as2)
         $ throwError $ "Mismatching constructor arg lengths between "
                         ++ pretty (In (Con c1 as1)) ++ " and "
                         ++ pretty (In (Con c2 as1))
       let (plics1,as1') = unzip as1
           (plics2,as2') = unzip as2
       unless (plics1 == plics2)
         $ throwError $ "Mismatching plicities when unifying "
             ++ pretty (In (Con c1 as1)) ++ " with "
             ++ pretty (In (Con c2 as2))
       return $ zipWith
                  Equation
                  (map instantiate0 as1')
                  (map instantiate0 as2')
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
  equate (RecordType fields1 tele1) (RecordType fields2 tele2) =
    do unless (fields1 == fields2)
         $ throwError $ "Record types have different field names: "
             ++ pretty (In (RecordType fields1 tele1))
             ++ " and "
             ++ pretty (In (RecordType fields2 tele2))
       ns <- freshRelTo (namesTelescope tele1) context
       let xs = map (Var . Free) ns
           as1 = instantiateTelescope tele1 xs
           as2 = instantiateTelescope tele2 xs
       unless (length as1 == length as2)
         $ throwError $ "Records have different number of fields: "
             ++ pretty (In (RecordType fields1 tele1))
             ++ " and "
             ++ pretty (In (RecordType fields2 tele2))
       return $ zipWith Equation as1 as2
  equate (RecordCon fields1) (RecordCon fields2) =
    do unless (length fields1 == length fields2)
         $ throwError $ "Records have different number of fields: "
             ++ pretty (In (RecordCon fields1))
             ++ " and "
             ++ pretty (In (RecordCon fields2))
       let (fs1,ms1) = unzip fields1
           (fs2,ms2) = unzip fields2
       unless (fs1 == fs2)
         $ throwError $ "Records have different field names: "
             ++ pretty (In (RecordCon fields1))
             ++ " and "
             ++ pretty (In (RecordCon fields2))
       return $ zipWith
                  Equation
                  (map instantiate0 ms1)
                  (map instantiate0 ms2)
  equate (RecordProj r1 x1) (RecordProj r2 x2) =
    do unless (x1 == x2)
         $ throwError $ "Record projections have different names: "
             ++ pretty (In (RecordProj r1 x1))
             ++ " and "
             ++ pretty (In (RecordProj r2 x2))
       return [Equation (instantiate0 r1) (instantiate0 r2)]
  equate (QuotedType res1 a1) (QuotedType res2 a2) =
    do unless (res1 == res2)
         $ throwError $ "Quoted types have different reset locations: "
             ++ pretty (In (QuotedType res1 a1))
             ++ " and "
             ++ pretty (In (QuotedType res2 a2))
       return [Equation (instantiate0 a1) (instantiate0 a2)]
  equate (Quote m1) (Quote m2) =
    return [Equation (instantiate0 m1) (instantiate0 m2)]
  equate (Unquote m1) (Unquote m2) =
    return [Equation (instantiate0 m1) (instantiate0 m2)]
  equate (Continue m1) (Continue m2) =
    return [Equation (instantiate0 m1) (instantiate0 m2)]
  equate (Shift res1 m1) (Shift res2 m2) =
    do unless (res1 == res2)
         $ throwError "Shifts have different reset locations."
       return [Equation (instantiate0 m1) (instantiate0 m2)]
  equate (Reset res1 m1) (Reset res2 m2) =
    do unless (res1 == res2)
         $ throwError "Resets have different reset locations."
       return [Equation (instantiate0 m1) (instantiate0 m2)]
  equate l r =
    throwError $ "Cannot unify " ++ pretty (In l) ++ " with " ++ pretty (In r)





-- | Equating case motives as a special helper for the main 'equate' method.

equateCaseMotive :: CaseMotive -> CaseMotive -> Elaborator [Equation Term]
equateCaseMotive mot1@(CaseMotive tele1) mot2@(CaseMotive tele2) =
  do ns <- freshRelTo (namesBindingTelescope tele1) context
     let xs = map (Var . Free) ns
         (as1, b1) = instantiateBindingTelescope tele1 xs
         (as2, b2) = instantiateBindingTelescope tele2 xs
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