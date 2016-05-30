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

module Require.Core.Term where

import Utils.ABT
import Utils.Names
import Utils.Plicity
import Utils.Pretty
import Utils.Telescope

import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Data.List (intercalate)







-- | Terms in this variant are the same as the Modular variant, except that
-- we also now have terms for record types, record terms, and record
-- projection.

data TermF r
  = Defined Name
  | Ann r r
  | Type
  | Fun Plicity r r
  | Lam Plicity r
  | App Plicity r r
  | Con Name [(Plicity,r)]
  | Case [r] (CaseMotiveF r) [ClauseF r]
  | RecordType [String] (Telescope r)
  | RecordCon [(String,r)]
  | RecordProj r String
  | QuotedType [String] r
  | Quote r
  | Unquote r
  | Continue r
  | Shift String r
  | Reset String r
  | Require r r
  deriving (Functor,Foldable,Traversable)


instance Eq1 TermF where
  eq1 (Defined n) (Defined n') =
    n == n'
  eq1 (Ann m t) (Ann m' t') =
    m == m' && t == t'
  eq1 Type Type =
    True
  eq1 (Fun plic a sc) (Fun plic' a' sc') =
    plic == plic' && a == a' && sc == sc'
  eq1 (Lam plic sc) (Lam plic' sc') =
    plic == plic' && sc == sc'
  eq1 (App plic f x) (App plic' f' x') =
    plic == plic' && f == f' && x == x'
  eq1 (Con c ms) (Con c' ms') =
    c == c' && ms == ms'
  eq1 (Case ms motive clauses) (Case ms' motive' clauses') =
    ms == ms' && eq1 motive motive'
      && length clauses == length clauses'
      && all (uncurry eq1) (zip clauses clauses')
  eq1 (RecordType fields tele) (RecordType fields' tele') =
    fields == fields' && eq1 tele tele'
  eq1 (RecordCon fs) (RecordCon fs') =
    fs == fs'
  eq1 (RecordProj m x) (RecordProj m' x') =
    x == x' && m == m'
  eq1 (QuotedType resets a) (QuotedType resets' a') =
    resets == resets' && a == a'
  eq1 (Quote m) (Quote m') =
    m == m'
  eq1 (Unquote m) (Unquote m') =
    m == m'
  eq1 (Continue m) (Continue m') =
    m == m'
  eq1 (Shift res m) (Shift res' m') =
    res == res' && m == m'
  eq1 (Reset res m) (Reset res' m') =
    res == res' && m == m'
  eq1 (Require a sc) (Require a' sc') =
    a == a' && sc == sc'
  eq1 _ _ =
    False


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
  deriving (Functor,Foldable,Traversable)


instance Eq1 CaseMotiveF where
  eq1 (CaseMotive tele) (CaseMotive tele') =
    eq1 tele tele'


type CaseMotive = CaseMotiveF (Scope TermF)


data ClauseF r
  = Clause [PatternF r] r
  deriving (Functor,Foldable,Traversable)


instance Eq1 ClauseF where
  eq1 (Clause ps sc) (Clause ps' sc') =
    length ps == length ps'
      && all (uncurry eq1) (zip ps ps')
      && sc == sc'


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


instance Eq a => Eq1 (PatternFF a) where
  eq1 (ConPat c ps) (ConPat c' ps') =
    c == c' && ps == ps'
  eq1 (AssertionPat m) (AssertionPat m') =
    m == m'
  eq1 MakeMeta MakeMeta =
    True
  eq1 _ _ =
    False


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


instance Bitraversable PatternFF where
  bisequenceA (ConPat c ps) =
    ConPat c <$> sequenceA [ (,) plic <$> p
                           | (plic,p) <- ps
                           ]
  bisequenceA (AssertionPat m) =
    AssertionPat <$> m
  bisequenceA MakeMeta =
    pure MakeMeta


-- | 'PatternF' is the type of pattern shaped containers for terms. The
-- bifunctoriality and bifoldability of 'PatternFF' gives rise to the
-- functoriality and foldability of 'PatternF', meaning we can use it as a
-- sub-sort of term shape. This ought to be generic, but Haskell can'

newtype PatternF a = PatternF { unwrapPatternF :: Scope (PatternFF a) }


instance Eq1 PatternF where
  eq1 (PatternF x) (PatternF x') = x == x'


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

instance Traversable PatternF where
  sequenceA (PatternF sc) = PatternF <$> bisequenceScopeF sc


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

recordTypeH :: [(String,Term)] -> Term
recordTypeH fas = In (RecordType fs (telescopeH fs as))
  where
    (fs,as) = unzip fas

recordConH :: [(String,Term)] -> Term
recordConH fields = In (RecordCon [ (f, scope [] a) | (f,a) <- fields ])

recordProjH :: Term -> String -> Term
recordProjH r x = In (RecordProj (scope [] r) x)

quotedTypeH :: [String] -> Term -> Term
quotedTypeH resets a = In (QuotedType resets (scope [] a))

quoteH :: Term -> Term
quoteH m = In (Quote (scope [] m))

unquoteH :: Term -> Term
unquoteH m = In (Unquote (scope [] m))

continueH :: Term -> Term
continueH m = In (Continue (scope [] m))

shiftH :: String -> Term -> Term
shiftH res m = In (Shift res (scope [] m))

resetH :: String -> Term -> Term
resetH res m = In (Reset res (scope [] m))

requireH :: String -> Term -> Term -> Term
requireH x a m = In (Require (scope [] a) (scope [x] m))





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
  | RecFieldType | RecFieldVal | RecProjArg
  | QuotedTypeArg | QuoteArg | UnquoteArg
  | ContinueArg | ShiftArg | ResetArg
  | RequireType | RequireBody
  deriving (Eq)


instance Parens Term where
  type Loc Term = TermParenLoc
  
  parenLoc (Var _) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Defined _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Ann _ _)) =
    [FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveRet
    ,ClauseBody,RecFieldVal,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In Type) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Fun _ _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
    ]
  parenLoc (In (Lam _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
    ]
  parenLoc (In (App _ _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Impl,ConArg Impl
    ,CaseArg,MotiveArg,MotiveRet,ClauseBody,RecFieldType,RecFieldVal
    ,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Con _ [])) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Con _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Impl,ConArg Impl
    ,CaseArg,MotiveArg,MotiveRet,ClauseBody,RecFieldType,RecFieldVal
    ,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Case _ _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (RecordType _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (RecordCon _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (RecordProj _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,AssertionPatArg,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg
    ,QuoteArg,UnquoteArg,ContinueArg,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (QuotedType _ _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Impl,ConArg Impl
    ,CaseArg,MotiveArg,MotiveRet,ClauseBody,RecFieldType,RecFieldVal
    ,ShiftArg,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Quote _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg,ContinueArg,ShiftArg
    ,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Unquote _)) =
    [AnnTerm,AnnType,FunArg,FunRet,LamBody,AppFun,AppArg Expl,AppArg Impl
    ,ConArg Expl,ConArg Impl,CaseArg,MotiveArg,MotiveRet,ClauseBody
    ,RecFieldType,RecFieldVal,RecProjArg,QuotedTypeArg,ContinueArg,ShiftArg
    ,ResetArg,RequireType,RequireBody
    ]
  parenLoc (In (Continue _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
    ]
  parenLoc (In (Shift _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
    ]
  parenLoc (In (Reset _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
    ]
  parenLoc (In (Require _ _)) =
    [AnnType,FunArg,FunRet,LamBody,AppArg Impl,ConArg Impl,CaseArg,MotiveArg
    ,MotiveRet,ClauseBody,RecFieldType,RecFieldVal,ShiftArg,ResetArg
    ,RequireType,RequireBody
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
  parenRec (In (RecordType fields (Telescope ascs))) =
    case types of
      [] -> "Rec {}"
      fs -> "Rec { " ++ intercalate ", " fs ++ " }"
    where
      types =
        zipWith
          (\field asc ->
            field ++ " : " ++ parenthesize (Just RecFieldType) (body asc))
          fields
          ascs
  parenRec (In (RecordCon fields)) =
    if null fields
       then "{}"
       else "{ "
            ++ intercalate
                 ", "
                 [ x ++ " = "
                     ++ parenthesize
                          (Just RecFieldVal)
                          (instantiate0 t)
                 | (x,t) <- fields
                 ]
            ++ " }"
  parenRec (In (RecordProj r x)) =
    parenthesize
      (Just RecProjArg)
      (instantiate0 r)
    ++ "." ++ x
  parenRec (In (QuotedType resets a)) =
    "Quoted[" ++ intercalate "," resets ++ "] "
      ++ parenthesize (Just QuotedTypeArg) (instantiate0 a)
  parenRec (In (Quote m)) =
    "`" ++ parenthesize (Just QuoteArg) (instantiate0 m)
  parenRec (In (Unquote m)) =
    "~" ++ parenthesize (Just UnquoteArg) (instantiate0 m)
  parenRec (In (Continue m)) =
    "continue " ++ parenthesize (Just ContinueArg) (instantiate0 m)
  parenRec (In (Shift res m)) =
    "shift " ++ res ++ " in "
      ++ parenthesize (Just ShiftArg) (instantiate0 m)
  parenRec (In (Reset res m)) =
    "reset " ++ res ++ " in "
      ++ parenthesize (Just ResetArg) (instantiate0 m)
  parenRec (In (Require a sc)) =
    "require " ++ head (names sc) ++ " : "
      ++ parenthesize (Just RequireType) (instantiate0 a)
      ++ " in " ++ parenthesize (Just RequireBody) (body sc)





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