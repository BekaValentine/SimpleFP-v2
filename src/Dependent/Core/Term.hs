{-# OPTIONS -Wall #-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}







-- | This module defines the terms of the dependently typed lambda calculus.

module Dependent.Core.Term where

import Utils.ABT
import Utils.Pretty
import Utils.Telescope

import Data.Bifoldable
import Data.Bifunctor
import Data.List (intercalate)







-- | Dependent terms are like non-dependent terms, with the addition of the
-- terms that represent types, including 'Type' (the type of types). There are
-- no type constructors, because they now are just normal constructors.

data TermF r
  = Defined String
  | Ann r r
  | Type
  | Fun r r
  | Lam r
  | App r r
  | Con String [r]
  | Case [r] (CaseMotiveF r) [ClauseF r]
  deriving (Functor,Foldable)


type Term = ABT TermF


type TermTelescope = Telescope (Scope TermF)


-- | A case motive is a telescope that describes the arguments of a case
-- expression and the expression as a whole. Because this variant is
-- dependently typed, the type of a whole case expression can depend on the
-- particular values given to it, so something similar to a @Pi@ type is
-- necessary. For more on the use of motives with case expressions, you can
-- look at Agda's motive-based case function (tho importantly, Agda makes
-- pattern matching functions primary, and case is defined in terms of this).
-- For a more general look at motives, McBride's Elimination with a Motive is
-- a very good resource.

newtype CaseMotiveF r = CaseMotive (Telescope r)
  deriving (Functor,Foldable)


type CaseMotive = CaseMotiveF (Scope TermF)


data ClauseF r
  = Clause [PatternF r] r
  deriving (Functor,Foldable)


type Clause = ClauseF (Scope TermF)


-- | Patterns in the dependent variant have to be able to have scope all of
-- their own, because they can be binders, but they also need to have
-- assertion terms which are themselves capable of being binders. Because of
-- this, we need to define pattern constructions with a doubly-parameterized
-- type. The @r@ parameter will be used for the recursive occurrences of
-- patterns inside patterns, while the @a@ parameter will be used similar to
-- the @a@ parameter in a 'Fix'-based definition of 'List':
--
-- @
--    data ListF a r = Nil | Cons a r
--
--    type List a = Fix (ListF a)
-- @
--
-- However, the fixed/ABTed pattern will itself be used as a kind of shape,
-- just like lists, 'ClauseF', 'CaseMotiveF', etc. are used above. So the type
-- 'PatternFF' is the shapes of pattern shapes, perversely.

data PatternFF a r
  = ConPat String [r]
  | AssertionPat a
  deriving (Functor,Foldable)


instance Bifunctor PatternFF where
  bimap _ g (ConPat s xs) = ConPat s (map g xs)
  bimap f _ (AssertionPat x) = AssertionPat (f x)


instance Bifoldable PatternFF where
  bifoldMap _ g (ConPat _ xs) = foldMap g xs
  bifoldMap f _ (AssertionPat x) = f x


instance Bizippable PatternFF where
  bizip (ConPat c rs) (ConPat c' rs')
    | c == c' && length rs == length rs' =
      Just ([], zip rs rs')
    | otherwise = Nothing
  bizip (AssertionPat a) (AssertionPat a') =
    Just ([(a,a')], [])
  bizip _ _ = Nothing


-- | 'PatternF' is the type of pattern shaped containers for terms. The
-- bifunctoriality and bifoldability of 'PatternFF' gives rise to the
-- functoriality and foldability of 'PatternF', meaning we can use it as a
-- sub-sort of term shape. This ought to be generic, but Haskell can'

newtype PatternF a = PatternF { unwrapPatternF :: Scope (PatternFF a) }


type Pattern = ABT (PatternFF Term)


instance Functor PatternF where
  fmap f (PatternF x) = PatternF (translateScope (first f) x)


instance Foldable PatternF where
  foldMap f (PatternF x) = foldScope fmAlgVar (fmAlgRec f) fmAlgSc x
    where
      fmAlgVar :: Monoid m => Variable -> m
      fmAlgVar _ = mempty
      
      fmAlgRec :: Monoid m => (a -> m) -> PatternFF a m -> m
      fmAlgRec g = bifoldMap g id
      
      fmAlgSc :: Monoid m => Int -> m -> m
      fmAlgSc _ = id


-- | Because patterns need to have two domains of binders that essentially
-- bind the same variables — the binders in the assertions, and the binders
-- in the scopes themselves — we benefit from being able to bind both at once.
-- The 'patternScope' function does precisely this, by first binding the
-- assertion scopes, and then by binding the pattern scope.

patternScope :: [String] -> Pattern -> PatternF (Scope TermF)
patternScope xs = pattern . assertions
  where
    assertions :: Pattern -> ABT (PatternFF (Scope TermF))
    assertions = translate (first (scope xs))
    
    pattern :: ABT (PatternFF (Scope TermF)) -> PatternF (Scope TermF)
    pattern = PatternF . scope xs


-- | We can simultaneously instantiate the pattern scope and the inner
-- asserted term scopes.

patternInstantiate :: PatternF (Scope TermF)
                   -> [ABT (PatternFF Term)]
                   -> [Term]
                   -> ABT (PatternFF Term)
patternInstantiate p ps xs = pattern (assertions p)
  where
    assertions :: PatternF (Scope TermF) -> PatternF Term
    assertions = fmap (\sc -> instantiate sc xs)
    
    pattern :: PatternF Term -> ABT (PatternFF Term)
    pattern (PatternF x) = instantiate x ps


-- | It's also useful to be able to strip off binders to get a sort of body.

patternBody :: PatternF (Scope TermF) -> Pattern
patternBody (PatternF sc) = translate (first body) (body sc)


annH :: Term -> Term -> Term
annH m t = In (Ann (scope [] m) (scope [] t))

funH :: String -> Term -> Term -> Term
funH x a b = In (Fun (scope [] a) (scope [x] b))

lamH :: String -> Term -> Term
lamH x b = In (Lam (scope [x] b))

appH :: Term -> Term -> Term
appH f x = In (App (scope [] f) (scope [] x))

conH :: String -> [Term] -> Term
conH c as = In (Con c (map (scope []) as))

caseH :: [Term] -> CaseMotive -> [Clause] -> Term
caseH as mot cls = In (Case (map (scope []) as) mot cls)

caseMotiveH :: [String] -> [Term] -> Term -> CaseMotive
caseMotiveH xs as b = CaseMotive (telescopeH xs as b)

clauseH :: [String] -> [Pattern] -> Term -> Clause
clauseH xs ps b = Clause (map (patternScope xs) ps) (scope xs b)

conPatH :: String -> [Pattern] -> Pattern
conPatH c ps = In (ConPat c (map (scope []) ps))

assertionPatH :: Term -> Pattern
assertionPatH m = In (AssertionPat m)





-- | Terms have a variety of positions in which they can have subterms.

data TermParenLoc
  = AnnTerm | AnnType
  | FunArg | FunRet
  | LamBody | AppFun | AppArg
  | ConArg | CaseArg | MotiveArg | MotiveRet | ClauseBody
  | AssertionPatArg
  deriving (Eq)


instance Parens Term where
  type Loc Term = TermParenLoc
  
  parenLoc (Var _) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg
    ,ConArg,CaseArg,MotiveArg,MotiveRet,ClauseBody,AssertionPatArg
    ]
  parenLoc (In (Defined _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg
    ,ConArg,CaseArg,MotiveArg,MotiveRet,ClauseBody,AssertionPatArg
    ]
  parenLoc (In (Ann _ _)) =
    [FunArg,FunRet,LamBody,CaseArg,MotiveRet,ClauseBody]
  parenLoc (In Type) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg
    ,ConArg,CaseArg,MotiveArg,MotiveRet,ClauseBody,AssertionPatArg
    ]
  parenLoc (In (Fun _ _)) =
    [AnnType,FunArg,FunRet,LamBody,CaseArg,MotiveArg,MotiveRet,ClauseBody]
  parenLoc (In (Lam _)) =
    [AnnType,FunArg,FunRet,LamBody,CaseArg,MotiveArg,MotiveRet,ClauseBody]
  parenLoc (In (App _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,CaseArg,MotiveArg
    ,MotiveRet ,ClauseBody
    ]
  parenLoc (In (Con _ [])) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg
    ,ConArg,CaseArg,MotiveArg,MotiveRet,ClauseBody,AssertionPatArg
    ]
  parenLoc (In (Con _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody
    ]
  parenLoc (In (Case _ _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg
    ,ConArg,CaseArg,MotiveArg,MotiveRet,ClauseBody,AssertionPatArg
    ]
  
  parenRec (Var v) =
    name v
  parenRec (In (Defined n)) = n
  parenRec (In (Ann m ty)) =
    parenthesize (Just AnnTerm) (instantiate0 m)
      ++ " : " ++ parenthesize (Just AnnType) (instantiate0 ty)
  parenRec (In Type) = "Type"
  parenRec (In (Fun a sc)) =
    "(" ++ unwords (names sc)
      ++ " : " ++ parenthesize (Just FunArg) (instantiate0 a)
      ++ ") -> " ++ parenthesize (Just FunRet) (body sc)
  parenRec (In (Lam sc)) =
    "\\" ++ unwords (names sc)
      ++ " -> " ++ parenthesize (Just LamBody)
                     (body sc)
  parenRec (In (App f a)) =
    parenthesize (Just AppFun) (instantiate0 f)
      ++ " " ++ parenthesize (Just AppArg) (instantiate0 a)
  parenRec (In (Con c [])) = c
  parenRec (In (Con c as)) =
    c ++ " " ++ unwords (map (parenthesize (Just ConArg).instantiate0) as)
  parenRec (In (Case ms mot cs)) =
    "case "
      ++ intercalate
           " || "
           (map (parenthesize (Just CaseArg).instantiate0) ms)
      ++ " motive " ++ pretty mot
      ++ " of " ++ intercalate " | " (map auxClause cs) ++ " end"
    where
      auxClause (Clause pscs sc)
        = intercalate " || " (map (pretty.body.unwrapPatternF.fmap body) pscs)
            ++ " -> " ++ parenthesize (Just ClauseBody) (body sc)





data CaseMotiveParenLoc


instance Eq CaseMotiveParenLoc where
  _ == _ = True


instance Parens CaseMotive where
  type Loc CaseMotive = CaseMotiveParenLoc
  
  parenLoc _ = []
  
  parenRec (CaseMotive (Telescope ascs bsc)) =
    binders ++ " || " ++ pretty (body bsc)
    where
      binders =
        intercalate " || "
          (zipWith
             (\n a -> "(" ++ n ++ " : " ++ a ++ ")")
             ns
             as)
      as = map (pretty.body) ascs
      ns = names bsc





data PatternParenLoc
  = ConPatArg
  deriving (Eq)


instance Parens Pattern where
  type Loc Pattern = PatternParenLoc
  
  parenLoc (Var _)               = [ConPatArg]
  parenLoc (In (ConPat _ []))    = [ConPatArg]
  parenLoc (In (ConPat _ _))      = []
  parenLoc (In (AssertionPat _)) = [ConPatArg]
  
  parenRec (Var v) =
    name v
  parenRec (In (ConPat c [])) = c
  parenRec (In (ConPat c ps)) =
    c ++ " "
      ++ unwords (map (parenthesize (Just ConPatArg).instantiate0) ps)
  parenRec (In (AssertionPat m)) =
    "." ++ parenthesize (Just AssertionPatArg) m