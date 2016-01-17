{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}







-- | This module defines how to evaluate terms in the dependently typed lambda
-- calculus.

module Dependent.Core.Evaluation where

import Control.Monad.Except

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Pretty
import Utils.Telescope
import Dependent.Core.Term







-- | Pattern matching for case expressions.

matchPattern :: Pattern -> Term -> Maybe [Term]
matchPattern (Var _) v = Just [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM matchPattern (map body ps) (map body as))
matchPattern (In (AssertionPat _)) v = Just [v]
matchPattern _ _ = Nothing

matchPatterns :: [Pattern] -> [Term] -> Maybe [Term]
matchPatterns [] [] =
  Just []
matchPatterns (p:ps) (m:ms) =
  do vs <- matchPattern p m
     vs' <- matchPatterns ps ms
     return $ vs ++ vs'
matchPatterns _ _ = Nothing

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ = Nothing
matchClauses (Clause pscs sc:cs) ms =
  case matchPatterns (map patternBody pscs) ms of
    Nothing -> matchClauses cs ms
    Just vs -> Just (instantiate sc vs)





-- | Standard eager evaluation.

instance Eval (Env String Term) Term where
  eval (Var v) =
    return $ Var v
  eval (In (Defined x)) =
    do env <- environment
       case lookup x env of
         Nothing -> throwError $ "Unknown constant/defined term: " ++ x
         Just m  -> return m
  eval (In (Ann m _)) =
    eval (instantiate0 m)
  eval (In Type) =
    return $ In Type
  eval (In (Fun a sc)) =
    do ea <- underM eval a
       esc <- underM eval sc
       return $ In (Fun ea esc)
  eval (In (Lam sc)) =
    do esc <- underM eval sc
       return $ In (Lam esc)
  eval (In (App f a)) =
    do ef <- eval (instantiate0 f)
       ea <- eval (instantiate0 a)
       case ef of
         In (Lam sc) -> eval (instantiate sc [ea])
         _      -> return $ appH ef ea
  eval (In (Con c as)) =
    do eas <- mapM (eval.instantiate0) as
       return $ conH c eas
  eval (In (Case ms mot cs)) =
    do ems <- mapM eval (map instantiate0 ms)
       case matchClauses cs ems of
         Nothing ->
           if any (\p -> case p of { (In (Con _ _)) -> False ; _ -> True })
                  ems
           then do
             emot <- eval mot
             ecs <- mapM eval cs
             return $ caseH ems emot ecs
           else throwError $ "Incomplete pattern match: "
                          ++ pretty (In (Case ms mot cs))
         Just b  -> eval b


instance Eval (Env String Term) CaseMotive where
  eval (CaseMotive (Telescope ascs bsc)) =
    do eascs <- mapM (underM eval) ascs
       ebsc <- underM eval bsc
       return $ CaseMotive (Telescope eascs ebsc)


instance Eval (Env String Term) Clause where
  eval (Clause pscs bsc) =
    do epscs <- mapM eval pscs
       ebsc <- underM eval bsc
       return $ Clause epscs ebsc


instance Eval (Env String Term) (PatternF (Scope TermF)) where
  eval (PatternF x) =
    do ex <- underM eval x
       return $ PatternF ex


instance Eval (Env String Term) (ABT (PatternFF (Scope TermF))) where
  eval (Var v) =
    return $ Var v
  eval (In (ConPat c ps)) =
    do eps <- mapM (underM eval) ps
       return $ In (ConPat c eps)
  eval (In (AssertionPat m)) =
    do em <- underM eval m
       return $ In (AssertionPat em)