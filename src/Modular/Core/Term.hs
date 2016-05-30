{-# OPTIONS -Wall #-}

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}







-- | This module defines the terms of the dependently typed lambda calculus.

module Modular.Core.Term where

import Utils.ABT
import Utils.Names
import Utils.Plicity
import Utils.Pretty
import Utils.Telescope

import Data.Bifoldable
import Data.Bifunctor
import Data.List (intercalate)







-- | Terms in this variant are the same as the Dependent Implicit variant,
-- except that names can be also of the form @M.foo@ to refer to a module.

data TermF r
  = Defined Name
  | Ann r r
  | Type
  | Fun Plicity r r
  | Lam Plicity r
  | App Plicity r r
  | Con Name [(Plicity,r)]
  | Case [r] (CaseMotiveF r) [ClauseF r]
  deriving (Functor,Foldable)


type Term = ABT TermF


-- | A case motive is a telescope that describes the arguments of a case
-- expression and the expression as a whole. Because this variant is
-- dependently typed, the type of a whole case expression can depend on the
-- particular values given to it, so something similar to a @Pi@ type is
-- necessary. For more on the use of motives with case expressions, you can
-- look at Agda's motive-based case function (tho importantly, Agda makes
-- pattern matching functions primary, and case is defined in terms of this).
-- For a more general look at motives, McBride's Elimination with a Motive is
-- a very good resource.

newtype CaseMotiveF r = CaseMotive (BindingTelescope r)
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
  = ConPat Name [(Plicity,r)]
  | AssertionPat a
  | MakeMeta
  deriving (Functor,Foldable,Traversable)


instance Bifunctor PatternFF where
  bimap _ g (ConPat s xs) = ConPat s [ (plic,g x) | (plic,x) <- xs ]
  bimap f _ (AssertionPat x) = AssertionPat (f x)
  bimap _ _ MakeMeta = MakeMeta


instance Bifoldable PatternFF where
  bifoldMap _ g (ConPat _ xs) = foldMap (g.snd) xs
  bifoldMap f _ (AssertionPat x) = f x
  bifoldMap _ _ MakeMeta = mempty


instance Bizippable PatternFF where
  bizip (ConPat c rs0) (ConPat c' rs0')
    | c == c' && length rs0 == length rs0' =
      let (plics,rs) = unzip rs0
          (plics',rs') = unzip rs0'
      in if (plics == plics')
            then Just ([], zip rs rs')
            else Nothing
    | otherwise = Nothing
  bizip (AssertionPat a) (AssertionPat a') =
    Just ([(a,a')], [])
  bizip MakeMeta MakeMeta = Just ([],[])
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

funH :: Plicity -> String -> Term -> Term -> Term
funH plic x a b = In (Fun plic (scope [] a) (scope [x] b))

lamH :: Plicity -> String -> Term -> Term
lamH plic x b = In (Lam plic (scope [x] b))

appH :: Plicity -> Term -> Term -> Term
appH plic f x = In (App plic (scope [] f) (scope [] x))

conH :: Name -> [(Plicity,Term)] -> Term
conH c as = In (Con c [ (plic, scope [] a) | (plic,a) <- as ])

caseH :: [Term] -> CaseMotive -> [Clause] -> Term
caseH as mot cls = In (Case (map (scope []) as) mot cls)

caseMotiveH :: [String] -> [Term] -> Term -> CaseMotive
caseMotiveH xs as b = CaseMotive (bindingTelescopeH xs as b)

clauseH :: [String] -> [Pattern] -> Term -> Clause
clauseH xs ps b = Clause (map (patternScope xs) ps) (scope xs b)

conPatH :: Name -> [(Plicity,Pattern)] -> Pattern
conPatH c ps = In (ConPat c [ (plic, scope [] p) | (plic,p) <- ps ])

assertionPatH :: Term -> Pattern
assertionPatH m = In (AssertionPat m)





-- | Terms have a variety of positions in which they can have subterms. Due
-- to plicities, both 'AppArg' and 'ConArg' have plicity arguments as well.
-- 'FunArg' doesn't need one because the notation always wraps with either
-- parens or braces, independent of what the argument type is.

data TermParenLoc
  = AnnTerm | AnnType
  | FunArg | FunRet
  | LamBody | AppFun | AppArg Plicity
  | ConArg Plicity | CaseArg | MotiveArg | MotiveRet | ClauseBody
  | AssertionPatArg
  deriving (Eq)


instance Parens Term where
  type Loc Term = TermParenLoc
  
  parenLoc (Var _) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl, ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg
    ]
  parenLoc (In (Defined _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl, ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg
    ]
  parenLoc (In (Ann _ _)) =
    [FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveRet
    ,ClauseBody
    ]
  parenLoc (In Type) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl, ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg
    ]
  parenLoc (In (Fun _ _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody
    ]
  parenLoc (In (Lam _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody
    ]
  parenLoc (In (App _ _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Impl,ConArg Impl
    ,CaseArg,MotiveArg,MotiveRet ,ClauseBody
    ]
  parenLoc (In (Con _ [])) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg
    ]
  parenLoc (In (Con _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Impl,ConArg Impl
    ,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ]
  parenLoc (In (Case _ _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg
    ]
  
  parenRec (Var v) =
    name v
  parenRec (In (Defined n)) = showName n
  parenRec (In (Ann m ty)) =
    parenthesize (Just AnnTerm) (instantiate0 m)
      ++ " : " ++ parenthesize (Just AnnType) (instantiate0 ty)
  parenRec (In Type) = "Type"
  parenRec (In (Fun plic a sc)) =
    wrap
      plic
      (unwords (names sc) 
         ++ " : " ++ parenthesize (Just FunArg) (instantiate0 a))
      ++ " -> " ++ parenthesize (Just FunRet) (body sc)
    where
      wrap Expl x = "(" ++ x ++ ")"
      wrap Impl x = "{" ++ x ++ "}"
  parenRec (In (Lam plic sc)) =
    "\\" ++ wrap plic (unwords (names sc))
      ++ " -> " ++ parenthesize (Just LamBody)
                     (body sc)
    where
      wrap Expl x = x
      wrap Impl x = "{" ++ x ++ "}"
  parenRec (In (App plic f a)) =
    parenthesize (Just AppFun) (instantiate0 f)
      ++ " " ++ wrap plic
                     (parenthesize
                       (Just (AppArg plic))
                       (instantiate0 a))
    where
      wrap Expl x = x
      wrap Impl x = "{" ++ x ++ "}"
  parenRec (In (Con c [])) = showName c
  parenRec (In (Con c as)) =
    showName c ++ " "
      ++ unwords [ wrap plic
                        (parenthesize
                          (Just (ConArg plic))
                          (instantiate0 a))
                 | (plic,a) <- as
                 ]
    where
      wrap Expl x = x
      wrap Impl x = "{" ++ x ++ "}"
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
  
  parenRec (CaseMotive (BindingTelescope ascs bsc)) =
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
  = ConPatArg Plicity
  deriving (Eq)


instance Parens Pattern where
  type Loc Pattern = PatternParenLoc
  
  parenLoc (Var _)               = [ConPatArg Expl, ConPatArg Impl]
  parenLoc (In (ConPat _ []))    = [ConPatArg Expl, ConPatArg Impl]
  parenLoc (In (ConPat _ _))     = [ConPatArg Impl]
  parenLoc (In (AssertionPat _)) = [ConPatArg Expl, ConPatArg Impl]
  parenLoc (In MakeMeta)         = [ConPatArg Expl, ConPatArg Impl]
  
  parenRec (Var v) =
    name v
  parenRec (In (ConPat c [])) = showName c
  parenRec (In (ConPat c ps)) =
    showName c ++ " "
      ++ unwords [ wrap plic
                        (parenthesize
                          (Just (ConPatArg plic))
                          (instantiate0 p))
                 | (plic,p) <- ps
                 ]
    where
      wrap Expl x = x
      wrap Impl x = "{" ++ x ++ "}"
  parenRec (In (AssertionPat m)) =
    "." ++ parenthesize (Just AssertionPatArg) m
  parenRec (In MakeMeta) = "?makemeta"