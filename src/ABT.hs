{-# OPTIONS -Wall #-}



-- | This module defines a kind of abstract binding tree (ABT). It uses a type
-- similar to the 'Fix' type, but with an added constructor for variables, and
-- an intermediate type 'Scope' for representing (possibly empty) binders.
-- For uniformity, every argument to a construct is a 'Scope', even args that
-- normally aren't seen as scopes. For example, whereas normally you might
-- expect that a pair has the form 'pair(M;N)' (using the PFPL notation),
-- with these ABTs, it has the form 'pair([].M;[].N)' where the pair elements
-- are binders with an empty list of bound variables. This avoids the need to
-- make two different types available to the class of constructions, one for
-- terms and one for scopes.

module ABT where

import Data.List (elemIndex)





-- | 'Term' is like 'Fix', but with the addition of tools for binders. Like
-- 'Fix', we have a parameter 'f' for functors that define the shape of the
-- constructors for the type of interest. In this sense, then, the subset
-- of elements that have no variables and non-binding 'Scope's is just a
-- kind of least fixed point, in the F-algebra sense. The addition of
-- variables and scopes simply introduces new constructors in the right
-- places to represent binding. It's similar to 'Free' for the free monad
-- construction, but the variable parameter is fixed to be 'Variable'.
--
-- The particular choices for 'f' can be simple polynomial functors, such as
-- 
-- 'data LC a = Pair a a | Fst a | Snd a | Lam a | App a a'
--
-- as for the a simple lambda calculus with pairs and functions, or it can be
-- more complex, such as
--
-- 'data LC a = ... | Con String [a] | Case a [(Pattern, a)]'
--
-- which has constructed data (eg 'Con "True" []' for 'True'), as well as
-- case expressions with a list of clauses, represented by pairs of patterns
-- and associated clause bodies.
--
-- The choice to represent ABTs this way was to make this kind of
-- representation possible, without simultaneously forcing every kind of
-- construct (lists, clauses, etc.) into the ABT type.

data Term f
  = Var Variable
  | In (f (Scope f))


-- | The 'shift' function appropriately increments a term's free variables,
-- to handle substitution under binders. Any 'Bound' variable inside a term
-- that gets substituted under a binder needs to still point to its own
-- binder higher up, or else it'll be captured. The 'l' argument of 'shift'
-- represents how many bound variables in the substituted term the 'shift' has
-- passed under, while the 'i' represents how many new bound variables there
-- are in the scope that's being substituted into.
--
-- For example, consider the function term '\x. (\y.\z.y) x'. This can
-- be normalized to '\x -> \z -> x' by beta reducing the inner application.
-- To do this, we need to substitute 'x' for 'y' in '\z -> y'. But 'x' is a
-- bound variable, bound by the outer lambda, so we need to avoid capture, by
-- shifting it appropriately. With de Bruijn indices, want to turn the term
-- '\.(\.\.1)0' into the term '\.\.1'. The index for 'x' has to shift from '0'
-- to '1' because it's being used under the binder for 'z'. This is what the
-- 'i' argument to 'shift' represents.
--
-- Similarly, if we had also put a binder around 'x', as in the term
-- '\x. (\y.\z.y) (\w.x)' we need to track that as well. This should normalize
-- to '\x.\z.\w.x'. With de Bruijn indices, '\. (\.\.1) (\.1)' should become
-- the term '\.\.\.2'. The variable 'x' initially was coded as '1', but shifts
-- to '2', as expected. However, if we had normalized '\x. (\y.\z.y) (\w.w)'
-- which with de Bruijn indexes is '\. (\.\.1) (\.0)', we expect to get back
-- '\x.\z.\w.w' which with de Bruin indexes is '\.\.\.0'. Notice that although
-- the variable 'w' corresponds to the index '0', the 'shift' function must
-- leave it unchanged. So not all bound variables are shifted, only those that
-- were bound outside of any new binders that 'shift' passes under. This is
-- what the variable 'l' represents in 'shift'.

shift :: Functor f => Int -> Int -> Term f -> Term f
shift l i (Var (Bound n j)) | j > l =
  Var (Bound n (i+j))
shift _ _ (Var v) = Var v
shift l i (In x) = In (fmap (shiftScope l i) x)


-- | Substitution is just variant of the bind operation for the 'Free' monad,
-- but with monadic parameter fixed.

subst :: Functor f => (Variable -> Term f) -> Term f -> Term f
subst f (Var v) = f v
subst f (In x) = In (fmap (substScope f) x)





-- | Three types of variables are used. 'Named' variables are for
-- user-supplied names that can be abstracted for binding, or can be left
-- free for use as names for defined terms, and other such things. 'Bound'
-- variables are de Bruijn indexes, and are used only in the scope of the
-- binder that binds the index. 'Generated' variables are for variables
-- that are "bound" by a context, and should be used for globally unique
-- temporary identifiers. All three have string values that represent the
-- stored display name of the variable, for pretty printing.

data Variable
  = Named String
  | Bound String Int
  | Generated String Int


-- | The name of a variable.

name :: Variable -> String
name (Named n)       = n
name (Bound n _)     = n
name (Generated n _) = n


-- | Equality of variables is by the parts which identify them, so names for
-- 'Named' variables, and identifying numbers for 'Bound' and 'Generated'.

instance Eq Variable where
  Named x       == Named y       = x == y
  Bound _ i     == Bound _ j     = i == j
  Generated _ i == Generated _ j = i == j
  _             == _             = False


-- | We increment a bound variable by 'i' by adding 'i' to its index. This is
-- used when performing substitution, as explained above.

increment :: Int -> Variable -> Variable
increment i (Bound n v) = Bound n (v+i)
increment _ v = v


-- | We also need to decrement variables during substitution, as below.

decrement :: Int -> Variable -> Variable
decrement i (Bound n v) = Bound n (v-i)
decrement _ v = v





-- | A 'Scope f' is a list of bound variable names used for both display
-- purposes and to track how many bound variables there are, along with a
-- 'Term f' for the body of the scope. a value 'Scope ["x","y"] m' corresponds
-- to a PFPL scope of the form 'x,y.m'

data Scope f = Scope [String] (Term f)


-- | When shifting a scope, we keep track of the number of new variables that
-- are brought into scope, so the number of variables bound by the scope is
-- added to the current value of 'l' in the recursive call.

shiftScope :: Functor f => Int -> Int -> Scope f -> Scope f
shiftScope l i (Scope ns x) = Scope ns (shift (l+length ns) i x)


-- | Substitution for scopes is slightly nuanced. The 'f' function is the
-- environment that defines the substitution, but when going under a scope,
-- it's necessary to decrement the variables before doing lookup, to adjust
-- for the fact that the environment performs a lookup for variables in the
-- scope around this one and needs to therefore adjust inner variables
-- appropriately. For example, when substituting for '0' into the de Bruijn
-- term '(\.1) 0', the index '1' should also be substituted for, since it
-- refers to the same variable. Therefore, when the environment reaches it,
-- it has to first decrement '1' to '0' and then perform the lookup. It's also
-- necessary to shift the result of the substitution by however many variables
-- the scope binds, to avoid capture.

substScope :: Functor f => (Variable -> Term f) -> Scope f -> Scope f
substScope f (Scope ns x) =
  Scope ns (subst f' x)
  where
    i = length ns
    f' = shift 0 i . f . decrement i


-- | A smart constructor that creates a 'Scope f' while also performing
-- actual binding of named variables. This can technically bind 'Bound'
-- variables as well, so it's important to avoid ever making bound variables
-- manually, instead using only 'scope' to create bound variables.

scope :: Functor f => [Variable] -> Term f -> Scope f
scope vs b = Scope (map name vs) (subst f b)
  where
    l = length vs
    f v = case elemIndex v vs of
            Nothing ->
              Var v
            Just i ->
              Var (Bound (name v) (l - i - 1))


-- | Instantiating a scope simply means substituting an appropriate number
-- of terms in for the variables bound by the scope.

instantiate :: Functor f => Scope f -> [Term f] -> Term f
instantiate (Scope ns b) xs
  | length ns /= length xs = error "Cannot substitute along differing numbers of arguments."
  | null ns = b
  | otherwise = subst f b
    where
      f (Bound _ i) | i < length ns = xs !! (length xs - i - 1)
      f v = Var v