{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}







-- | This module defines a number of tools for use with elaborators.

module Utils.Elaborator where

import Utils.Vars

import Control.Lens
import Control.Monad.State







type MonadElab s m = MonadState s m





-- | 'getElab' is a mnemonic for looking up the value of a lens on state.

getElab :: MonadState s m => Lens' s a -> m a
getElab = use





-- | 'putElab' is a mnemonic for replacing the value of a lens on state.

putElab :: MonadState s m => Lens' s a -> a -> m ()
putElab = assign





-- | Given a lens that focuses on a list, we can add new elements to the list.

addElab :: MonadState s m => Lens' s [a] -> [a] -> m ()
addElab l xs = l %= (xs ++)





-- | Given a lens that focuses on a list, we can temporarily add new elements
-- to the list for some computation.

extendElab :: MonadState s m => Lens' s [a] -> [a] -> m b -> m b
extendElab l xs m = do oldXs <- getElab l
                       addElab l xs
                       v <- m
                       putElab l oldXs
                       return v





-- | We can freshen variables relative to any context-like list.

freshRelTo :: MonadState s m
            => [String] -> Lens' s [(FreeVar,a)] -> m [FreeVar]
freshRelTo ns l = do ctx <- getElab l
                     let oldNs = [ n' | (FreeVar n',_) <- ctx ]
                     return $ map FreeVar (freshen oldNs ns)