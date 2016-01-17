{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}







-- | This module defines telescopes.

module Utils.Telescope where

import Utils.ABT
import Utils.Vars

import Data.Functor.Classes
import Data.List (inits)







-- | A telescope is a series of binders, ending in a binder. This is used for 
-- constructions that have iterated binding over an ultimate scope, such as
-- case motives.

data Telescope a
  = Telescope [a] a
  deriving (Functor,Foldable)


instance Eq1 Telescope where
  eq1 (Telescope as b) (Telescope as' b') =
    as == as' && b == b'


namesTelescope :: Telescope (Scope f) -> [String]
namesTelescope (Telescope _ bsc) = names bsc


telescopeH :: (Functor f, Foldable f)
           => [String] -> [ABT f] -> ABT f -> Telescope (Scope f)
telescopeH xs as b = Telescope ascs bsc
  where
    xss = inits xs
    scs = zipWith scope xss (as ++ [b])
    ascs = init scs
    bsc = last scs





-- | It's often the case that we need to instantiate a telescope of scopes
-- with a sequence of values. For example, when checking a constructor in a
-- dependently typed language, we need to insteantiate with the arguments.
-- This function abstracts out the common part.
--
-- To understand how this is implemented, consider the following examples for
-- what certain things could be:
--
-- @
--    ms  = [M0, M1, M2, ...]
--    mss = [ []
--          , [M0]
--          , [M0,M1]
--          , ...
--          ]
--    ascs ++ [bsc]  =  [ ().A0
--                      , (x0).A1
--                      , (x0,x1).A2
--                      , ...
--                      , (x0,...,xn).B
--                      ]
--    asb = [ A0
--          , [M0/x0]A1
--          , [M0/x0,M1/x1]A2
--          , ...
--          , [M0/x0,...,Mn/xn]B
--          ]
-- @

instantiateTelescope :: (Functor f, Foldable f)
                     => Telescope (Scope f) -> [ABT f] -> ([ABT f], ABT f)
instantiateTelescope (Telescope ascs bsc) ms = (as,b)
  where
    mss = inits ms
    asb = zipWith instantiate (ascs ++ [bsc]) mss
    as = init asb
    b = last asb


-- | It's also often useful to perform a kind of unbinding with a collection
-- of free variables, which is essentially instantiation along with zipping
-- the parts of the telescope together with their instantiated names. This is
-- useful, for instance, when checking that telescope-based constructions such
-- as case motives are wellformed, which requires that we not only have the
-- instantiated motive argument types but also the new context extensions that
-- are necessary to check that each motive argument type is indeed a type.
--
-- The example values for @ms@, @mss@, @ascs ++ [bsc]@, and @asb@ are mostly
-- the same as for 'instantiateTelescope' module 'Var . Free': @asb@ is not
-- some terms in place of the variables, but now its basically just the bodies
-- of each scope (possibly renamed, according to the input variables). But we
-- also need to consider the following:
-- 
-- @
--    zip ns as = [ (x0,A0), (x1,A1), (x2,A2), ... ]
--    inits (zip ns as) =
--      [ []
--      , [ (x0,A0) ]
--      , [ (x0,A0), (x1,A1) ]
--      , [ (x0,A0), (x1,A1), (x2,A2) ]
--      , ...
--      ]
--    zip (inits (zip ns as)) asb =
--      [ ( [] , A0 )
--      , ( [(x0,A0)] , A1 )
--      , ( [(x0,A0),(x1,A1)] , A2 )
--      , ...
--      , ( [(x0,A0),...,(xn,An)] , B )
--      ]
-- @
--
-- So what's going on is that we're more or less pulling off the variables for
-- each scope and revealing the body of the scope, along with the relevant new
-- typing declarations for its variables.

instantiateTelescopeNames :: (Functor f, Foldable f)
                          => Telescope (Scope f)
                          -> [FreeVar]
                          -> [([(FreeVar, ABT f)], ABT f)]
instantiateTelescopeNames (Telescope ascs bsc) ns = cs
  where
    mss = inits (map (Var . Free) ns)
    asb = zipWith instantiate (ascs ++ [bsc]) mss
    as = init asb
    cs = zip (inits (zip ns as)) asb