{-# OPTIONS -Wall #-}







module Dependent.Core.ConSig where

import Utils.ABT
import Utils.Pretty (pretty)
import Utils.Telescope
import Dependent.Core.DeclArg
import Dependent.Core.Term







newtype ConSig = ConSig (BindingTelescope (Scope TermF))


instance Show ConSig where
  show (ConSig (BindingTelescope ascs bsc)) =
    binders ++ " " ++ pretty (body bsc)
    where
      binders =
        unwords
          (zipWith
             (\n a -> "(" ++ n ++ " : " ++ a ++ ")")
             ns
             as)
      as = map (pretty.body) ascs
      ns = names bsc


conSigH :: [DeclArg] -> Term -> ConSig
conSigH declas b = ConSig (bindingTelescopeH xs as b)
  where (xs,as) = unzip [ (x,a) | DeclArg x a <- declas ]


freeToDefinedConSig :: ConSig -> ConSig
freeToDefinedConSig (ConSig tele) =
  ConSig (fmap (freeToDefinedScope (In . Defined)) tele)