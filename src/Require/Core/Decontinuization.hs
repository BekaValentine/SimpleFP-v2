{-# OPTIONS -Wall #-}







-- | This module defines the tools for decontinuizing terms.

module Require.Core.Decontinuization where

import Utils.ABT hiding (shift)
import Require.Core.Term

import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.State








-- | Binary composition to make applicative style more convenient.

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
f .: g = \x y -> f (g x y)


-- | Trinary composition to make applicative style more convenient.

(.::) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
f .:: g = \x y z -> f (g x y z)





-- | A @Continuer@ is a higher-order representation of the body of a shift,
-- which contains continue points. A term such as @foo x * continue x@ would
-- correspond to a function   @\c -> foo x * c x@. We can therefore represent
-- this by using a reader.

type Continuer a = Reader (Term -> Term) a


-- | This is the core of what makes a continuer go. Every constructor is
-- propagated algebraically except @Continue@ which is swapped for @continue@,
-- constructing the basic @Continuer@.

continue :: Term -> Continuer Term
continue x = reader ($ x)





-- | We transform a term into a @Continuer@ by just replacing every maximal
-- term @Continue x@ with @continue x@, leaving everything else alone.

makeContinuer :: Term -> Continuer Term
makeContinuer (Var v) = pure (Var v)
makeContinuer (In (Continue m)) = continue (instantiate0 m)
makeContinuer (In x) = In <$> traverse (underF makeContinuer) x







-- | Another important type is @Shifter@. This is a tyoe that makes it easy
-- to replace the @Shift@ terms with their appropriate reset value. However,
-- since there are multiple shifts inside any given reset, we track which
-- shifted term we're at when we replace it, hence the use of @State@.
-- Additionally, because the replacement terms are not yet known, we instead
-- need to compose up a function that will pick the appropriate one from a
-- list.

newtype Shifter a = Shifter { runShifter :: State Int ([Term] -> a, [Term]) }


-- | A shifter is evaluated by evaluating it's state starting with 0.

evalShifter :: Shifter a -> ([Term] -> a, [Term])
evalShifter (Shifter x) = evalState x 0


instance Functor Shifter where
  fmap f x = Shifter $ do
               (g,e) <- runShifter x
               return (f.g, e)


instance Applicative Shifter where
  pure x = Shifter (pure (const x, []))
  f <*> x = Shifter $ do
              (f',e) <- runShifter f
              (x',e') <- runShifter x
              return (\ms -> f' ms (x' ms), e ++ e')




-- | The @shift@ function is the core of shifting behavior, much like
-- @continue@ is the core of continuing behavior. @shift@ will put its term
-- into the list of shifted terms to return, and the functiont to look up its
-- replacement does so by projecting out the current index according to the
-- state, which is itself incremented.

shift :: Term -> Shifter Term
shift x = Shifter $ do
            i <- get
            put (i+1)
            return ((!! i), [x]) 





-- | We transform a term into a @Shifter@ by just replacing every maximal
-- term @Shift res x@ with @shift x@, leaving everything else alone.

makeShifter :: Term -> Shifter Term
makeShifter (Var v) = pure (Var v)
makeShifter (In (Shift _ m)) = shift (instantiate0 m)
makeShifter (In x) = In <$> traverse (underF makeShifter) x





-- | We can reset a number of shifts by collecting up the maximal shifts in
-- an expression, converting their bodies to the appropriate continuers,
-- then sequencing the corresponding continuized values, and then running that
-- sequenced continuized value on the continuation. We repeat this until there
-- are no shifts to reset, at which point we're done'.

reset :: Term -> Term
reset x
  | null shifts = m []
  | otherwise =
    let ks = mapM (cont . runReader . makeContinuer) shifts
    in reset (runCont ks m)
  where
    (m,shifts) = evalShifter (makeShifter x)





-- | A term is decontinuized by resetting every reset term in a bottom up way.

decontinuize :: Term -> Term
decontinuize (Var v) = Var v
decontinuize (In (Reset _ m)) = reset (decontinuize (instantiate0 m))
decontinuize (In x) = In (fmap (under decontinuize) x)