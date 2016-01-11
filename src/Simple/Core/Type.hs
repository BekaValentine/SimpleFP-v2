{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | The types of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module Simple.Core.Type where

import Utils.ABT
import Utils.Pretty
import Utils.Vars





-- | Types can be type constructors, functions, or meta-variables.
-- Meta-variable types are used for type checking with unification.
-- Variables are also not used in this setting, but we address them anyway.

data TypeF r
  = TyCon String
  | Fun r r
  | Meta MetaVar
  deriving (Eq,Functor,Foldable)


type Type = ABT TypeF





tyConH :: String -> Type
tyConH c = In (TyCon c)

funH :: Type -> Type -> Type
funH a b = In (Fun (scope [] a) (scope [] b))

metaH :: MetaVar -> Type
metaH v = In (Meta v)


-- | Metas can be instantiated via substitution

instantiateMetas :: (MetaVar -> Maybe Type) -> Type -> Type
instantiateMetas _ (Var v) =
  Var v
instantiateMetas _ (In (TyCon c)) =
  In (TyCon c)
instantiateMetas f (In (Fun a b)) =
  In (Fun (instantiateMetas f `under` a)
          (instantiateMetas f `under` b))
instantiateMetas f (In (Meta v)) =
  case f v of
    Nothing -> In (Meta v)
    Just t -> t





-- | There are two possible recursive locations within a type, so there are
-- two 'TypeParenLoc's for the parenthesizer to use.

data TypeParenLoc = FunLeft | FunRight
  deriving (Eq)


-- | Everything can be de-parenthesized everywhere, except for functions.
-- A function can only be de-parenthesized on the right of a function arrow.

instance Parens Type where
  type Loc Type = TypeParenLoc
  
  parenLoc (Var _)        = [FunLeft,FunRight]
  parenLoc (In (TyCon _)) = [FunLeft,FunRight]
  parenLoc (In (Fun _ _)) = [FunRight]
  parenLoc (In (Meta _))  = [FunLeft,FunRight]

  parenRec (Var v)        = name v
  parenRec (In (TyCon c)) = c
  parenRec (In (Fun a b)) =
    parenthesize (Just FunLeft) (instantiate0 a)
      ++ " -> "
      ++ parenthesize (Just FunRight) (instantiate0 b)
  parenRec (In (Meta (MetaVar i))) =
    "?" ++ show i