{-# OPTIONS -Wall #-}







module Modular.Core.ConSig where

import Utils.ABT
import Utils.Names
import Utils.Plicity
import Utils.Pretty (pretty)
import Utils.Telescope
import Modular.Core.DeclArg
import Modular.Core.Term







data ConSig = ConSig [Plicity] (Telescope (Scope TermF))


instance Show ConSig where
  show (ConSig plics (Telescope ascs bsc)) =
    binders ++ " " ++ pretty (body bsc)
    where
      binders =
        unwords
          (zipWith
             (\n (plic,a) -> wrap plic (n ++ " : " ++ a))
             ns
             (zip plics as))
      as = map (pretty.body) ascs
      ns = names bsc
      
      wrap Expl x = "(" ++ x ++ ")"
      wrap Impl x = "{" ++ x ++ "}"


conSigH :: [DeclArg] -> Term -> ConSig
conSigH declas b = ConSig plics (telescopeH xs as b)
  where (plics,xas) = unzip [ (plic,(x,a)) | DeclArg plic x a <- declas ]
        (xs,as) = unzip xas


freeToDefinedConSig :: ConSig -> ConSig
freeToDefinedConSig (ConSig plics tele) =
  ConSig plics (fmap (freeToDefinedScope (In . Defined . BareLocal)) tele)