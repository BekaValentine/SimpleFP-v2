{-# OPTIONS -Wall #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}





-- | This module defines the tools required to correctly define a pretty
-- printer that can de-parenthesize expressions appropriately.

module Utils.Pretty where





class Parens a where
  
  -- | 'Loc a' is the type of names for the recursive locations in 'a'.
  type Loc a
  
  -- | 'parenLoc' maps each 'a' to a list of locations that permit it to
  -- be pretty printed without enclosing parentheses.
  parenLoc :: a -> [Loc a]
  
  -- | 'parenRec' pretty prints its argument without enclosing parentheses.
  parenRec :: a -> String


type Pretty a = (Parens a, Eq (Loc a))


-- | The 'parenthesize' function pretty prints its argument, inserting parens
-- appropriately, based on the location of the argument in the overall pretty
-- printing context, given by the argument 'l'. When 'l = Nothing', this
-- indicates that the term is the root term, and isn't inside a recursive
-- location, therefore requiring no parentheses.

parenthesize :: Pretty a => Maybe (Loc a) -> a -> String
parenthesize l x
  = let rec = parenRec x
    in case l of
         Nothing -> rec
         Just loc
           | loc `elem` parenLoc x -> rec
           | otherwise -> "(" ++ rec ++ ")"


pretty :: Pretty a => a -> String
pretty = parenthesize Nothing