{-# OPTIONS -Wall #-}







-- | This module defines the tools required for removing @require@ terms and
-- solving for their required values.

module Require.Core.RequireSolving where

import Utils.ABT
import Utils.Telescope
import Utils.Vars
import Require.Core.Evaluation
import Require.Core.Term

import Control.Monad.State
import Data.Foldable (traverse_)
import Data.List (inits,transpose,partition)
import Data.Map (Map,empty,alter,toList)







-- | A replace state has a metavar name store and a list of required types for
-- each name.

data ReplaceState = ReplaceState { nextMeta :: MetaVar
                                 , metaTypes :: [(MetaVar,Term)]
                                 }


newMeta :: Term -> State ReplaceState Term
newMeta a = do ReplaceState (MetaVar i) tys <- get
               put (ReplaceState (MetaVar (i+1))
                                 ((MetaVar i, a):tys))
               return (Var (Meta (MetaVar i)))





-- | We can remove requires by statefully traversing over them, replacing
-- their bound variable with a newly generated metavar.

removeRequires :: Term -> (Term, [(MetaVar,Term)])
removeRequires m0 =
  let (m',ReplaceState _ tys) =
        runState (go m0) (ReplaceState (MetaVar 0) [])
  in (m', tys)
  where
    go :: Term -> State ReplaceState Term
    go (Var v) = return (Var v)
    go (In (Require a sc)) =
      do m <- newMeta (instantiate0 a)
         go (instantiate sc [m])
    go (In x) = In <$> traverse (underF go) x





-- | A context is just a typing context like in type checking, a list of free
-- variables together with their types.

type Context = [(FreeVar,Term)]





-- | A scope state has a context for variables in scope, and a mapping from
-- metavars to a list of contexts it appears in.

data ScopeState = ScopeState { context :: Context
                             , metaContexts :: Map MetaVar [Context]
                             }


-- | In this setting, we need to user the declared names on the scopes
-- themselves, so when we extend a context, we'll also remove all other names
-- that conflict with the new ones.

extendContext :: Context -> State ScopeState a -> State ScopeState a
extendContext ctx sx =
  do s <- get
     let remadd oldCtx (v,a) = filter (\(v',_) -> v' /= v) oldCtx ++ [(v,a)]
         newCtx = foldl remadd (context s) ctx
     put s { context = newCtx }
     x <- sx
     s' <- get
     put s' { context = context s }
     return x





-- | We can capture the scopes of a metavariable by storing the current scope.

capture :: MetaVar -> State ScopeState ()
capture m =
  do s <- get
     put s { metaContexts =
               alter (\x -> case x of
                              Nothing -> Just [context s]
                              Just ctxs -> Just (context s : ctxs))
                     m
                     (metaContexts s)
           }





-- | Given a collection of contexts, we can find the subcontext that is common
-- to all of them.

commonSubcontext :: [Context] -> Context
commonSubcontext ctxs = go (transpose ctxs)
  where
    keepOrNot :: [(FreeVar,Term)] -> Maybe (FreeVar,Term)
    keepOrNot (x:xs)
      | all (x==) xs = Just x
    keepOrNot _ = Nothing
    
    go :: [[(FreeVar,Term)]] -> Context
    go [] = []
    go (xs:xss) =
      case keepOrNot xs of
        Nothing -> []
        Just x -> x : go xss





-- | We can capture the scopes of all the metavariables by traversing and
-- calling capture on them. We then keep only the subcontext that is a prefix
-- of every found context, because that's the stuff in scope that's common to
-- every location of the metavariable in question.

captureScopes :: Term -> [(MetaVar,Context)]
captureScopes m0 =
  let (_,ScopeState _ ctxs) =
        runState (go m0) (ScopeState [] empty)
      ctxs' = toList ctxs
  in [ (v, commonSubcontext ctx) | (v,ctx) <- ctxs' ]
  where
    go :: Term -> State ScopeState ()
    go (Var (Meta m)) =
      capture m
    go (Var _) =
      return ()
    go (In (Fun _ a sc)) =
      let v = FreeVar (head (names sc))
      in extendContext [(v,instantiate0 a)]
           $ go (instantiate sc [Var (Free v)])
    go (In (RecordType _ (Telescope ascs))) =
      goTele (map FreeVar (names (last ascs)))
             []
             ascs
    go (In x) =
      traverse_ (go . body) x
    
    goTele :: [FreeVar] -> [Term] -> [Scope TermF] -> State ScopeState ()
    goTele _ _ [] = return ()
    goTele vars acc (sc:scs) =
      do let ctx' = zip vars acc
             xs = [ Var (Free x) | x <- take (length (names sc)) vars ]
             a = instantiate sc xs
             acc' = acc ++ [a]
         extendContext ctx'
           $ go a
         goTele vars acc' scs





-- | We can sort solving problems by dependence.

sortProblems :: [(MetaVar,Term)] -> Maybe [(MetaVar,Term)]
sortProblems problems = go [] problems
  where
    go :: [MetaVar] -> [(MetaVar,Term)] -> Maybe [(MetaVar,Term)]
    go _ [] = Just []
    go prev xs =
      let (next,rest) =
            partition (\(_,a) -> all (`elem` prev) (metaVars a)) xs
      in if null next
         then Nothing
         else do rest' <- go (map fst next ++ prev) rest
                 return $ next ++ rest'
                 





-- | We can decompose a record into it's components by simply projecting.

decomposeRecord :: Term
                -> [String]
                -> Telescope (Scope TermF)
                -> [(Term,Term)]

decomposeRecord rec fields (Telescope ascs) =
  let projections = map (recordProjH rec) fields
      types = zipWith instantiate ascs (inits projections)
  in zip projections types





-- | We can decompose an arbitrary term by checking if its type lets it be
-- decomposed, and then recursing as necessary.

decompose :: Term -> Term -> [(Term,Term)]
decompose m (In (RecordType fields tele)) =
  do (m',a') <- decomposeRecord m fields tele
     decompose m' a'
decompose m a = [(m,a)]





-- | We can compose a record by incrementally composing fields.

composeRecord :: [(Term,Term)]
              -> [String]
              -> Telescope (Scope TermF)
              -> [Term]
composeRecord resources fields (Telescope ascs) =
  do fms <- go [] fields ascs
     return $ recordConH fms
  where
    go :: [Term] -> [String] -> [Scope TermF] -> [[(String,Term)]]
    go _ [] [] = [[]]
    go acc (f:fs) (sc:scs) =
      do let a = instantiate sc acc
         m <- compose resources a
         fms <- go (acc ++ [m]) fs scs
         return $ (f,m) : fms
    go _ _ _ =
      error $ "Can't compose malformed records. This case can only be reached"
        ++ " by trying to solve require expressions in a term that doesn't"
        ++ " type check."





-- | We can compose proofs by composing a record by fields, if a record is
-- required, or else by just looking up an appropriate term.

compose :: [(Term,Term)] -> Term -> [Term]
compose resources (In (RecordType fields tele)) =
  composeRecord resources fields tele
compose resources t =
  [ m | (m,t') <- resources, t == t' ]





-- | We can solve the requires in a term. The process looks roughly like this:
-- 
-- 1. Remove require terms, replacing them with metavariables
-- 2. Normalize the result, to push the metavariables into the right scopes
-- 3. Extract the scope for each metavariable
-- 4. Sort the metavariables by dependency
-- 5. Compose solutions in that order

solve :: [(Term,Term)] -> Term -> [Term]
solve resources0 m =
  let (m', problems) = removeRequires m
  in case evalTerm m' of
       Nothing -> []
       Just em -> case sortProblems problems of
         Nothing -> []
         Just sortedProblems ->
           let resourcesByMeta =
                 do (meta,ctx) <- captureScopes em
                    let newResources =
                          [ (Var (Free v), x)
                          | (v,x) <- ctx
                          ]
                    return (meta, resources0 ++ newResources)
           in do subs <- goSubstitutions resourcesByMeta sortedProblems
                 case evalTerm (substMetas subs em) of
                   Nothing -> []
                   Just em' -> [em']
  where
    goSubstitutions :: [(MetaVar,[(Term,Term)])]
                    -> [(MetaVar,Term)]
                    -> [[(MetaVar,Term)]]
    goSubstitutions _ [] = return []
    goSubstitutions resourcesByMeta ((meta,a):problems) =
      case lookup meta resourcesByMeta of
        Nothing -> []
        Just resources ->
          do solution <- compose resources a
             let newProblems =
                   map (\(meta',b) -> (meta',substMetas [(meta,solution)] b)) problems
             rest <- goSubstitutions resourcesByMeta newProblems
             return $ (meta,solution):rest