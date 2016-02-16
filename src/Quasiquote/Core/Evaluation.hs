{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}







-- | This module defines how to evaluate terms in the dependently typed lambda
-- calculus.

module Quasiquote.Core.Evaluation where

import Control.Monad.Except

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Names
import Utils.Pretty
import Utils.Telescope
import Quasiquote.Core.Term







-- | Because a case expression can be evaluated under a binder, it's necessary
-- to determine when a match failure is real or illusory. For example, if we
-- have the function @\x -> case x of { Zero -> True ; _ -> False }@, and
-- naively tried to match, the first clause would fail, because @x =/= Zero@,
-- and the second would succeed, reducing this function to @\x -> False@.
-- But this would be bad, because if we then applied this function to @Zero@,
-- the result is just @False@. But if we had applied the original function to
-- @Zero@ and evaluated, it would reduce to @True@. Instead, we need to know
-- more than just did the match succeed or fail, but rather, did it succeed,
-- definitely fail because of a constructor mismatch, or is it uncertain
-- because of insufficient information (e.g. a variable or some other
-- non-constructor expression). We can use this type to represent that
-- three-way distinction between definite matches, definite failures, and
-- unknown situations.

data MatchResult a
  = Success a
  | Unknown
  | Failure
  deriving (Functor)


instance Applicative MatchResult where
  pure = Success
  
  Success f <*> Success x = Success (f x)
  Unknown <*> _ = Unknown
  _ <*> Unknown = Unknown
  _ <*> _ = Failure


instance Monad MatchResult where
  return = Success
  
  Success x >>= f = f x
  Unknown >>= _ = Unknown
  Failure >>= _ = Failure


-- | Pattern matching for case expressions.

matchPattern :: Pattern -> Term -> MatchResult [Term]
matchPattern (Var _) v = Success [v]
matchPattern (In (ConPat c ps)) (In (Con c' as))
  | c == c' && length ps == length as =
    fmap concat
      $ forM (zip ps as)
          $ \((plic,psc),(plic',asc)) -> 
              if (plic == plic')
                 then matchPattern (body psc) (body asc)
                 else Failure
  | otherwise = Failure
matchPattern (In (AssertionPat _)) v = Success [v]
matchPattern _ _ = Unknown

matchPatterns :: [Pattern] -> [Term] -> MatchResult [Term]
matchPatterns [] [] =
  Success []
matchPatterns (p:ps) (m:ms) =
  do vs <- matchPattern p m
     vs' <- matchPatterns ps ms
     return $ vs ++ vs'
matchPatterns _ _ = Failure

matchClauses :: [Clause] -> [Term] -> MatchResult Term
matchClauses [] _ = Failure
matchClauses (Clause pscs sc:cs) ms =
  case matchPatterns (map patternBody pscs) ms of
    Failure -> matchClauses cs ms
    Unknown -> Unknown
    Success vs -> Success (instantiate sc vs)





-- | Standard eager evaluation.

type EnvKey = (String,String)

instance ParamEval Int (Env EnvKey Term) Term where
  paramEval _ (Var v) =
    return $ Var v
  paramEval 0 (In (Defined (Absolute m n))) =
    do env <- environment
       case lookup (m,n) env of
         Nothing -> throwError $ "Unknown constant/defined term: "
                              ++ showName (Absolute m n)
         Just x  -> paramEval 0 x
  paramEval _ (In (Defined (Absolute m n))) =
    return $ In (Defined (Absolute m n))
  paramEval _ (In (Defined x)) =
    throwError $ "Cannot evaluate the local name " ++ showName x
  paramEval 0 (In (Ann m _)) =
    paramEval 0 (instantiate0 m)
  paramEval l (In (Ann m t)) =
    do em <- paramEval l (instantiate0 m)
       et <- paramEval l (instantiate0 t)
       return $ annH em et
  paramEval _ (In Type) =
    return $ In Type
  paramEval l (In (Fun plic a sc)) =
    do ea <- underF (paramEval l) a
       esc <- underF (paramEval l) sc
       return $ In (Fun plic ea esc)
  paramEval l (In (Lam plic sc)) =
    do esc <- underF (paramEval l) sc
       return $ In (Lam plic esc)
  paramEval 0 (In (App plic f a)) =
    do ef <- paramEval 0 (instantiate0 f)
       ea <- paramEval 0 (instantiate0 a)
       case ef of
         In (Lam plic' sc)
           | plic == plic' -> paramEval 0 (instantiate sc [ea])
           | otherwise ->
               throwError "Mismatching plicities."
         _      -> return $ appH plic ef ea
  paramEval l (In (App plic f a)) =
    do ef <- paramEval l (instantiate0 f)
       ea <- paramEval l (instantiate0 a)
       return $ appH plic ef ea
  paramEval l (In (Con c as)) =
    do eas <- forM as $ \(plic,a) ->
                do ea <- paramEval l (instantiate0 a)
                   return (plic,ea)
       return $ conH c eas
  paramEval 0 (In (Case ms mot cs)) =
    do ems <- mapM (paramEval 0) (map instantiate0 ms)
       case matchClauses cs ems of
         Success b  -> paramEval 0 b
         Unknown -> 
           do emot <- paramEval 0 mot
              return $ caseH ems emot cs
         Failure ->
           throwError $ "Incomplete pattern match: "
                     ++ pretty (In (Case ms mot cs))
  paramEval l (In (Case ms mot cs)) =
    do ems <- mapM (paramEval l) (map instantiate0 ms)
       emot <- paramEval l mot
       ecs <- if l == 0
                 then return cs
                 else mapM (paramEval l) cs
       return $ caseH ems emot ecs
  paramEval l (In (RecordType fields (Telescope ascs))) =
    do eascs <- mapM (underF (paramEval l)) ascs
       return $ In (RecordType fields (Telescope eascs))
  paramEval l (In (RecordCon fields)) =
    do fields' <- forM fields $ \(f,m) -> do
                    em <- paramEval l (instantiate0 m)
                    return (f,em)
       return $ recordConH fields'
  paramEval 0 (In (RecordProj r x)) =
    do em <- paramEval 0 (instantiate0 r)
       case em of
         In (RecordCon fields) ->
           case lookup x fields of
             Nothing ->
               throwError $ "Unknown field '" ++ x ++ "' in record "
                            ++ pretty em
             Just m' ->
               return $ instantiate0 m'
         _ ->
           return $ recordProjH em x
  paramEval l (In (RecordProj r x)) =
    do em <- paramEval l (instantiate0 r)
       return $ recordProjH em x
  paramEval l (In (QuotedType a)) =
    do ea <- paramEval l (instantiate0 a)
       return $ quotedTypeH ea
  paramEval l (In (Quote m)) =
    do em <- paramEval (l+1) (instantiate0 m)
       return $ quoteH em
  paramEval 0 (In (Unquote _)) =
    throwError $ "Cannot evaluate an unquote at level 0. "
                 ++ "No such term should exist."
  paramEval 1 (In (Unquote m)) =
    do em <- paramEval 0 (instantiate0 m)
       case em of
         In (Quote m') -> return (instantiate0 m')
         _             -> return $ unquoteH em
  paramEval l (In (Unquote m)) =
    do em <- paramEval (l-1) (instantiate0 m)
       return $ unquoteH em




instance ParamEval Int (Env EnvKey Term) CaseMotive where
  paramEval l (CaseMotive (BindingTelescope ascs bsc)) =
    do eascs <- mapM (underF (paramEval l)) ascs
       ebsc <- underF (paramEval l) bsc
       return $ CaseMotive (BindingTelescope eascs ebsc)


instance ParamEval Int (Env EnvKey Term) Clause where
  paramEval l (Clause pscs bsc) =
    do epscs <- mapM (paramEval l) pscs
       ebsc <- underF (paramEval l) bsc
       return $ Clause epscs ebsc


instance ParamEval Int (Env EnvKey Term) (PatternF (Scope TermF)) where
  paramEval l (PatternF x) =
    do ex <- underF (paramEval l) x
       return $ PatternF ex


instance ParamEval Int (Env EnvKey Term) (ABT (PatternFF (Scope TermF))) where
  paramEval _ (Var v) =
    return $ Var v
  paramEval l (In (ConPat c ps)) =
    do eps <- forM ps $ \(plic,p) ->
                do ep <- underF (paramEval l) p
                   return (plic,ep)
       return $ In (ConPat c eps)
  paramEval l (In (AssertionPat m)) =
    do em <- underF (paramEval l) m
       return $ In (AssertionPat em)
  paramEval _ (In MakeMeta) =
    return $ In MakeMeta