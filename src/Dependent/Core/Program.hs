{-# OPTIONS -Wall #-}







-- | This module defines what it means to be a program in the dependently
-- typed lambda calculus.

module Dependent.Core.Program where

import Utils.Pretty
import Dependent.Core.ConSig
import Dependent.Core.DeclArg
import Dependent.Core.Term

import Data.List (intercalate)







-- | A program is just a series of 'Statement's.

newtype Program = Program [Statement]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)





-- | A 'Statement' is either a 'TypeDeclaration' or a 'TermDeclaration'.

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td





-- | A term can be declared either with a simple equality, as in
--
-- > let not : Bool -> Bool
-- >   = \b -> case b of
-- >           | True -> False
-- >           | False -> True
-- >           end
-- > end
--
-- or with a pattern match, as in
--
-- > let not : Bool -> Bool where
-- >   | not True = False
-- >   | not False = True
-- > end

data TermDeclaration
  = TermDeclaration String Term Term
  | WhereDeclaration String Term [([String],[Pattern],Term)]

instance Show TermDeclaration where
  show (TermDeclaration n ty def) =
    "let " ++ n ++ " : " ++ pretty ty ++ " = " ++ pretty def ++ " end"
  show (WhereDeclaration n ty preclauses) =
    "let " ++ n ++ " : " ++ pretty ty ++ " where "
      ++ intercalate " | " (map showPreclause preclauses)
    where
      showPreclause :: ([String],[Pattern],Term) -> String
      showPreclause (_,ps,b) =
        intercalate " || " (map (parenthesize Nothing) ps)
          ++ " -> " ++ pretty b





-- | A type is declared with a GADT-like notation, however instead of giving
-- the type of a constructor, as in Haskell or Agda, a constructor's signature
-- is given via exemplified application, as in:
--
-- @
--    data List (a : Type) where
--       | Nil : List a
--       | Cons (x : a) (xs : List a) : List a
--    end
-- @
--
-- Types with no constructors need no @where@:
--
-- > data Void end

data TypeDeclaration
  = TypeDeclaration String [DeclArg] [(String,ConSig)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon tyargs []) =
    "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (TypeDeclaration tycon tyargs alts) =
    "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " where"
      ++ concat [ "\n" ++ c ++ " : " ++ show sig | (c,sig) <- alts ]
      ++ "\nend"