{-# OPTIONS -Wall #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Utils.Eval where

import Control.Monad.Reader

type Evaluator e = ReaderT e (Either String)

environment :: Evaluator e e
environment = ask

class Eval e a where
  eval :: a -> Evaluator e a