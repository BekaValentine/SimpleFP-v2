{-# OPTIONS -Wall #-}



module Dependent.Core.DeclArg where

import Utils.Pretty
import Dependent.Core.Term



data DeclArg = DeclArg String Term

instance Show DeclArg where
  show (DeclArg x t) = "(" ++ x ++ " : " ++ pretty t ++ ")"