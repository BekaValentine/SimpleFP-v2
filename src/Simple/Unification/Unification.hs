{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}







-- | This module defines unification of simple types.

module Simple.Unification.Unification where

import Utils.ABT
import Utils.Pretty
import Utils.Unifier
import Simple.Core.Type
import Simple.Unification.Elaborator

import Control.Monad.Except







-- | Equating terms by trivial structural equations.

instance MonadUnify TypeF Elaborator where
  equate (TyCon tycon1) (TyCon tycon2) =
    do unless (tycon1 == tycon2)
         $ throwError $ "Mismatching type constructors "
                     ++ tycon1 ++ " and " ++ tycon2
       return []
  equate (Fun a1 b1) (Fun a2 b2) =
    return [ Equation (instantiate0 a1) (instantiate0 a2)
           , Equation (instantiate0 b1) (instantiate0 b2)
           ]
  equate l r =
    throwError $ "Cannot unify " ++ pretty (In l) ++ " with " ++ pretty (In r)