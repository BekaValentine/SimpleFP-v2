{-# OPTIONS -Wall #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}







-- This module defines the core types of a monadic elaborator.

module OpenDefs.Unification.Elaborator where

import Utils.Env
import Utils.Plicity
import Utils.Unifier
import Utils.Vars
import OpenDefs.Core.ConSig
import OpenDefs.Core.Term

import qualified Control.Lens as L
import Control.Monad.State







-- | A signature is a collection of constructors together with their
-- constructor signatures. This is used during type checking and elaboration
-- to define the underlying type theory.

type Signature = [((String,String),ConSig)]





-- | A definition consists of a declared name together with its definition
-- and its type.

type Definitions = [((String,String),(Term,Term))]

definitionsToEnvironment :: Definitions -> Env (String,String) Term
definitionsToEnvironment defs =
  [ (x,m) | (x,(m,_)) <- defs ]





-- | A context contains generated variables together with their display names,
-- and their declared types.

type Context = [(FreeVar,Term)]





-- | Aliases are just maps from local names to absolute names.

type Aliases = [(Either String (String,String), (String,String))]





-- | Open functions have to story their pattern matching definitions so they
-- can be re-built when new instances are added.

type OpenFunction = ((String,String),(Term,[Plicity],CaseMotive,[Clause]))





-- | The definition of the state to be carried by the type checking monad for
-- this particular variant.

data ElabState
  = ElabState
    { _signature :: Signature
    , _definitions :: Definitions
    , _context :: Context
    , _substitution :: Substitution TermF
    , _nextMeta :: MetaVar
    , _aliases :: Aliases
    , _moduleName :: String
    , _moduleNames :: [String]
    , _openData :: [(String,String)]
    , _openFunctions :: [OpenFunction]
    }
L.makeLenses ''ElabState


type Elaborator = StateT ElabState (Either String)


type TypeChecker = Elaborator


runElaborator :: Elaborator a
              -> Signature
              -> Definitions
              -> Context
              -> Aliases
              -> String
              -> [String]
              -> [(String,String)]
              -> [OpenFunction]
              -> Either String (a,ElabState)
runElaborator e sig defs ctx als modname mods odata ofuns =
  runStateT
    e
    (ElabState sig defs ctx [] (MetaVar 0) als modname mods odata ofuns)


runElaborator0 :: Elaborator a -> Either String (a,ElabState)
runElaborator0 e = runElaborator e [] [] [] [] "" [] [] []


when' :: Elaborator a -> Elaborator () -> Elaborator ()
when' e1 e2 = do s <- get
                 case runStateT e1 s of
                   Left _ -> return ()
                   Right _  -> e2