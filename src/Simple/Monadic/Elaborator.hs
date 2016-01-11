{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}







-- This module defines the core types of a monadic elaborator.

module Simple.Monadic.Elaborator where

import Utils.Elaborator
import Utils.Env
import Utils.Vars
import Simple.Core.ConSig
import Simple.Core.Term
import Simple.Core.Type

import Control.Monad.State







-- | A definition consists of a declared name together with its definition
-- and its type.

type Definitions = [(String,(Term,Type))]

definitionsToEnvironment :: Definitions -> Env String Term
definitionsToEnvironment defs
  = [ (x,m) | (x,(m,_)) <- defs ]





-- A context contains generated variables together with their display names,
-- and their declared types.

type Context = [(FreeVar,Type)]





-- The definition of the state to be carried by the type checking monad for
-- this particular variant.

data ElabState
  = ElabState
    { elabSig :: Signature
    , elabDefs :: Definitions
    , elabCtx :: Context
    }


instance ElaboratorState ElabState where
  type Sig ElabState = Signature
  type Defs ElabState = Definitions
  type Ctx ElabState = Context
  
  elaboratorSig = elabSig
  putElaboratorSig sig s = s { elabSig = sig }
  addElaboratorSig (Signature eTycons eConSigs) s =
    s { elabSig = Signature (tycons ++ eTycons) (conSigs ++ eConSigs) }
    where Signature tycons conSigs = elabSig s
  
  elaboratorDefs = elabDefs
  putElaboratorDefs defs s = s { elabDefs = defs }
  addElaboratorDefs edefs s = s { elabDefs = edefs ++ elabDefs s }
  
  elaboratorCtx = elabCtx
  putElaboratorCtx ctx s = s { elabCtx = ctx }
  addElaboratorCtx ectx s = s { elabCtx = ectx ++ elabCtx s }
  
  contextNames s = [ n | (FreeVar n,_) <- elabCtx s ]


type Elaborator a = StateT ElabState (Either String) a


type TypeChecker a = Elaborator a


runElaborator :: Elaborator a
              -> Signature
              -> Definitions
              -> Context
              -> Either String (a,ElabState)
runElaborator e sig defs ctx
  = runStateT e (ElabState sig defs ctx)


runElaborator0 :: Elaborator a -> Either String (a,ElabState)
runElaborator0 e = runElaborator e (Signature [] []) [] []


when' :: Elaborator a -> Elaborator () -> Elaborator ()
when' e1 e2 = do s <- get
                 case runStateT e1 s of
                   Left _ -> return ()
                   Right _  -> e2