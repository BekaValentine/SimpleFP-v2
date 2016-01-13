{-# OPTIONS -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}







-- This module defines the core types of a unification elaborator.

module Simple.Unification.Elaborator where

import Utils.Env
import Utils.Unifier
import Utils.Vars
import Simple.Core.ConSig
import Simple.Core.Term
import Simple.Core.Type

import qualified Control.Lens as L
import Control.Monad.State







-- | A signature is a collection of type constructors, and data constructors
-- together with their constructor signatures. This is used during type
-- checking and elaboration to define the underlying type theory.

data Signature
  = Signature
    { _typeConstructors :: [String]
    , _dataConstructors :: [(String,ConSig)]
    }
L.makeLenses ''Signature





-- | A definition consists of a declared name together with its definition
-- and its type.

type Definitions = [(String,(Term,Type))]

definitionsToEnvironment :: Definitions -> Env String Term
definitionsToEnvironment defs =
  [ (x,m) | (x,(m,_)) <- defs ]





-- | A context contains generated variables together with their types.

type Context = [(FreeVar,Type)]





-- | The definition of the state to be carried by the type checking monad for
-- this particular variant. We need only the bare minimum of a signature,
-- some defined terms, and a typing context.

data ElabState
  = ElabState
    { _signature :: Signature
    , _definitions :: Definitions
    , _context :: Context
    , _substitution :: Substitution TypeF
    , _nextMeta :: MetaVar
    }
L.makeLenses ''ElabState


type Elaborator = StateT ElabState (Either String)


type TypeChecker = Elaborator


runElaborator :: Elaborator a
              -> Signature
              -> Definitions
              -> Context
              -> Either String (a,ElabState)
runElaborator e sig defs ctx =
  runStateT e (ElabState sig defs ctx [] (MetaVar 0))


runElaborator0 :: Elaborator a -> Either String (a,ElabState)
runElaborator0 e = runElaborator e (Signature [] []) [] []


when' :: Elaborator a -> Elaborator () -> Elaborator ()
when' e1 e2 = do s <- get
                 case runStateT e1 s of
                   Left _ -> return ()
                   Right _  -> e2