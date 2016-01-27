{-# OPTIONS -Wall #-}



-- | A type that represents plicity, i.e. implicit and explicit.
module Utils.Plicity where



data Plicity = Expl | Impl
  deriving (Eq,Show)