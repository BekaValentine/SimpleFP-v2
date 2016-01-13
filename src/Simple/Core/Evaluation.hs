{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | This module defines how to evaluate terms in the simply typed lambda
-- calculus w/ non-parametric user defined types (eg Bool, Nat).

module Simple.Core.Evaluation where

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Pretty (pretty)
import Simple.Core.Term

import Control.Monad.Except





-- | Pattern matching for case expressions.

match :: Pattern -> Term -> Maybe [Term]
match (Var _) v = Just [v]
match (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat (zipWithM match (map body ps) (map body as))
match _ _ = Nothing

matchTerms :: [Pattern] -> [Term] -> Maybe [Term]
matchTerms ps zs = fmap concat (zipWithM match ps zs)

matchClauses :: [Clause] -> [Term] -> Maybe Term
matchClauses [] _ =
  Nothing
matchClauses (Clause pscs sc:cs) vs =
  case matchTerms (map body pscs) vs of
    Nothing -> matchClauses cs vs
    Just xs -> Just (instantiate sc xs)





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
  eval (In (Lam sc)) =
    return $ In (Lam sc)
  eval (In (App f a)) =
    do ef <- eval (instantiate0 f)
       ea <- eval (instantiate0 a)
       case ef of
         In (Lam sc) -> eval (instantiate sc [ea])
         _ -> return $ appH ef ea
  eval (In (Con c as)) =
    do eas <- mapM (eval . instantiate0) as
       return $ conH c eas
  eval (In (Case ms cs)) =
    do ems <- mapM (eval . instantiate0) ms
       case matchClauses cs ems of
         Nothing -> throwError $ "Incomplete pattern match: " ++ pretty (In (Case ms cs))
         Just b  -> eval b