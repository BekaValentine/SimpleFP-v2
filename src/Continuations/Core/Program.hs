{-# OPTIONS -Wall #-}







-- | This module defines what it means to be a program in the dependently
-- typed lambda calculus.

module Continuations.Core.Program where

import Utils.Names
import Utils.Plicity
import Utils.Pretty
import Continuations.Core.ConSig
import Continuations.Core.DeclArg
import Continuations.Core.Term

import Data.List (intercalate)







-- | A 'Statement' is either a 'TypeDeclaration' or a 'TermDeclaration'.

data Statement
  = TyDecl TypeDeclaration
  | TmDecl TermDeclaration
  | ResetDecl ResetDeclaration

instance Show Statement where
  show (TyDecl td) = show td
  show (TmDecl td) = show td
  show (ResetDecl rd) = show rd





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
  | WhereDeclaration String Term [([Plicity],([String],[Pattern],Term))]
  | LetFamilyDeclaration String [DeclArg] Term
  | LetInstanceDeclaration Name [([Plicity],([String],[Pattern],Term))]

instance Show TermDeclaration where
  show (TermDeclaration n ty def) =
    "let " ++ n ++ " : " ++ pretty ty ++ " = " ++ pretty def ++ " end"
  show (WhereDeclaration n ty preclauses)
    = "let " ++ n ++ " : " ++ pretty ty ++ " where "
        ++ intercalate " | " (map showPreclause preclauses)
    where
  show (LetFamilyDeclaration n args ty) =
    "let family " ++ n ++ " " ++ unwords (map show args)
      ++ " : " ++ pretty ty ++ " end"
  show (LetInstanceDeclaration n preclauses) =
    "let instance " ++ show n ++ " where "
      ++ intercalate " | " (map showPreclause preclauses)





-- | Since two different kinds of declarations can be defined via pattern
-- matching now, we extract out the utility function 'showPreclause' for that.

showPreclause :: ([Plicity],([String],[Pattern],Term)) -> String
showPreclause (plics,(_,ps,b))
  = intercalate
      " || "
      (map showPattern (zip plics ps))
    ++ " -> " ++ pretty b





-- | Similarly we extract out 'showPattern'.

showPattern :: (Plicity,Pattern) -> String
showPattern (Expl,p) = parenthesize (Just (ConPatArg Expl)) p
showPattern (Impl,p) = parenthesize (Just (ConPatArg Impl)) p





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
  | DataFamilyDeclaration String [DeclArg]
  | DataInstanceDeclaration Name [(String,ConSig)]

instance Show TypeDeclaration where
  show (TypeDeclaration tycon tyargs []) =
    "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (TypeDeclaration tycon tyargs alts) =
    "data " ++ tycon ++ concat (map (\x -> " " ++ show x) tyargs) ++ " where"
      ++ concat [ "\n" ++ c ++ " : " ++ show sig | (c,sig) <- alts ]
      ++ "\nend"
  show (DataFamilyDeclaration tycon tyargs) =
    "data family " ++ tycon
      ++ concat (map (\x -> " " ++ show x) tyargs) ++ " end"
  show (DataInstanceDeclaration tycon alts) =
    "data instance " ++ show tycon ++ " where"
      ++ concat [ "\n" ++ c ++ " : " ++ show sig
                | (c,sig) <- alts
                ]
      ++ "\nend"





-- | A continuation declaration declares the name of a reset point for
-- continuations, and its associated types.

data ResetDeclaration = ResetDeclaration String Term Term

instance Show ResetDeclaration where
  show (ResetDeclaration res a b) =
    "reset " ++ res ++ " from " ++ pretty a ++ " to " ++ pretty b ++ " end"





-- | Settings for hiding or using names from a module.

data HidingUsing
  = Hiding [String]
  | Using [String]





-- | Settings for opening a module's names for use.

data OpenSettings
  = OpenSettings
    { openModule :: String
    , openAs :: Maybe String
    , openHidingUsing :: Maybe HidingUsing
    , openRenaming :: [(String,String)]
    }

instance Show OpenSettings where
  show (OpenSettings m a hu r)
    = m ++ a' ++ hu' ++ r'
    where
      a' = case a of
             Nothing -> ""
             Just m' -> " as " ++ m'
      hu' = case hu of
              Nothing -> ""
              Just (Hiding ns) -> " hiding (" ++ intercalate "," ns ++ ")"
              Just (Using ns)  -> " using (" ++ intercalate "," ns ++ ")"
      r' = case r of
             [] -> ""
             _ -> " renaming ("
                  ++ intercalate
                       ", "
                       [ n ++ " to " ++ n'
                       | (n,n') <- r
                       ]
                  ++ ")"





-- | Modules with imports of other modules.

data Module
  = Module String [OpenSettings] [Statement]

instance Show Module where
  show (Module n [] stmts)
    = "module " ++ n ++ " where\n\n"
        ++ intercalate "\n\n" (map show stmts) ++ "\n\nend"
  show (Module n settings stmts)
    = "module " ++ n ++ " opening " ++ intercalate " | " (map show settings)
   ++ " where\n\n" ++ intercalate "\n\n" (map show stmts) ++ "\n\nend"





-- | A program is just a series of 'Module's.

newtype Program = Program [Module]

instance Show Program where
  show (Program stmts) = intercalate "\n\n" (map show stmts)