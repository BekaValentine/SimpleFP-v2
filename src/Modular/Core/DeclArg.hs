{-# OPTIONS -Wall #-}



module Modular.Core.DeclArg where

import Utils.Plicity
import Utils.Pretty
import Modular.Core.Term



data DeclArg = DeclArg Plicity String Term

instance Show DeclArg where
  show (DeclArg Expl x t) = "(" ++ x ++ " : " ++ pretty t ++ ")"
  show (DeclArg Impl x t) = "{" ++ x ++ " : " ++ pretty t ++ "}"