{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}





module Utils.Elaborator where

import Utils.Vars

import Control.Monad.State







-- * Elaborators



-- | Elaborators in general will have various things they need to keep track
-- of in the course of checking, inferring, etc., however they have at a
-- minimum a signature for their core type theory, a set of definitions for
-- declared names (especially checkers for programming languages), and a
-- context of variables in scope. Because this class represents an interface
-- for a state type, we need to both access and modify these values, hence
-- the methods.

class ElaboratorState s where
  type Sig s
  type Defs s
  type Ctx s
  
  elaboratorSig :: s -> Sig s
  putElaboratorSig :: Sig s -> s -> s
  addElaboratorSig :: Sig s -> s -> s
  
  elaboratorDefs :: s -> Defs s
  putElaboratorDefs :: Defs s -> s -> s
  addElaboratorDefs :: Defs s -> s -> s
  
  elaboratorCtx :: s -> Ctx s
  putElaboratorCtx :: Ctx s -> s -> s
  addElaboratorCtx :: Ctx s -> s -> s
  contextNames :: s -> [String]





-- | A functor is a 'MonadElab s' if it's a 'MonadState s', provided that 's'
-- is an 'ElaboratorState'

type MonadElab s m = (ElaboratorState s, Functor m, MonadState s m)



signature :: MonadElab s m => m (Sig s)
signature = fmap elaboratorSig get


putSignature :: MonadElab s m => Sig s -> m ()
putSignature sig = modify (putElaboratorSig sig)


addSignature :: MonadElab s m => Sig s -> m ()
addSignature sig = modify (addElaboratorSig sig)


extendSignature :: MonadElab s m => Sig s -> m a -> m a
extendSignature sig tc =
  do oldSig <- signature
     addSignature sig
     x <- tc
     putSignature oldSig
     return x



definitions :: MonadElab s m => m (Defs s)
definitions = fmap elaboratorDefs get


putDefinitions :: MonadElab s m => Defs s -> m ()
putDefinitions defs = modify (putElaboratorDefs defs)


addDefinitions :: MonadElab s m => Defs s -> m ()
addDefinitions defs = modify (addElaboratorDefs defs)


extendDefinitions :: MonadElab s m => Defs s -> m a -> m a
extendDefinitions defs tc =
  do oldDefs <- definitions
     addDefinitions defs
     x <- tc
     putDefinitions oldDefs
     return x



context :: MonadElab s m => m (Ctx s)
context = fmap elaboratorCtx get


putContext :: MonadElab s m => Ctx s -> m ()
putContext ctx = modify (putElaboratorCtx ctx)


addContext :: MonadElab s m => Ctx s -> m ()
addContext ctx = modify (addElaboratorCtx ctx)


extendContext :: MonadElab s m => Ctx s -> m a -> m a
extendContext ctx tc =
  do oldCtx <- context
     addContext ctx
     x <- tc
     putContext oldCtx
     return x


-- | It's useful to have a function that can give a set of fresh 'FreeVar's
-- given the ambient context.

freshVars :: MonadElab s m => [String] -> m [FreeVar]
freshVars ns =
  do s <- get
     let oldNs = contextNames s
     return $ map FreeVar (freshen oldNs ns)






-- * Type checkers with metavariables



-- | A type checker with metavariables has state that tracks the next
-- metavariable to generate, as well as a set of substitutions for
-- metavariables

class MetaState s where
  type Subs s
  
  elaboratorNextMeta :: s -> MetaVar
  putElaboratorNextMeta :: MetaVar -> s -> s
  
  elaboratorSubs :: s -> Subs s
  putElaboratorSubs :: Subs s -> s -> s
  addElaboratorSubs :: Subs s -> s -> s





-- | A 'MonadMetaElab s m' is just an elaborator who's state is a 'MetaState'.

type MonadMetaElab s m = (MetaState s, MonadElab s m)



newMetaVar :: MonadMetaElab s m => m MetaVar
newMetaVar =
  do MetaVar n <- fmap elaboratorNextMeta get
     modify (putElaboratorNextMeta (MetaVar (n+1)))
     return $ MetaVar n



substitution :: MonadMetaElab s m => m (Subs s)
substitution = fmap elaboratorSubs get


putSubstitution :: MonadMetaElab s m => Subs s -> m ()
putSubstitution subs = modify (putElaboratorSubs subs)


addSubstitution :: MonadMetaElab s m => Subs s -> m ()
addSubstitution subs = modify (addElaboratorSubs subs)