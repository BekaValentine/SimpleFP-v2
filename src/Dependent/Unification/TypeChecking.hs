{-# OPTIONS -Wall #-}







-- | A unification-based type checker.

module Dependent.Unification.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Eval
import Utils.Pretty
import Utils.Unifier
import Utils.Telescope
import Utils.Vars
import Dependent.Core.ConSig
import Dependent.Core.Evaluation ()
import Dependent.Core.Term
import Dependent.Unification.Elaborator
import Dependent.Unification.Unification ()

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State







-- | In the dependently typed variant, it's useful to have a type for normal
-- terms. While this type won't actually be representationally different, we
-- can use it to help ensure we're using normal forms in places where we want
-- them, such as the type arguments to checking.

newtype NormalTerm = NormalTerm { normTerm :: Term }


-- | It's useful to have a way of evaluating without having to constantly get
-- make an environment and run the evaluator manually.

evaluate :: SubstitutedTerm -> TypeChecker NormalTerm
evaluate (SubstitutedTerm m) =
  do defs <- getElab definitions
     case runReaderT (eval m) (definitionsToEnvironment defs) of
       Left e   -> throwError e
       Right m' -> return $ NormalTerm m'


-- | Similarly, it's also useful to be able to ensure that we're using terms
-- that have been substituted into. This doesn't exist in the monadic variant
-- because there's no unification going on.

newtype SubstitutedTerm = SubstitutedTerm Term

substitute :: Term -> TypeChecker SubstitutedTerm
substitute t = do subs <- getElab substitution
                  return $ SubstitutedTerm (substMetas subs t)


-- | We'd like to make sure that unification only happens to normal terms, so
-- we'll define a convenience function we can use.

unifyHelper :: NormalTerm -> NormalTerm -> TypeChecker ()
unifyHelper (NormalTerm x) (NormalTerm y) =
  unify substitution context x y


-- | We can get the consig of a constructor by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n con S@

typeInSignature :: String -> Elaborator ConSig
typeInSignature n =
  do consigs <- getElab signature
     case lookup n consigs of
       Nothing -> throwError $ "Unknown constructor: " ++ n
       Just t  -> return t


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n : A@

typeInDefinitions :: String -> Elaborator Term
typeInDefinitions x =
  do defs <- getElab definitions
     case lookup x defs of
       Nothing    -> throwError $ "Unknown constant/defined term: " ++ x
       Just (_,t) -> return t


-- | We can get the type of a free variable by looking in the context. This
-- corresponds to the judgment @Γ ∋ x : A true@

typeInContext :: FreeVar -> Elaborator Term
typeInContext v@(FreeVar n) =
  do ctx <- getElab context
     case lookup v ctx of
       Nothing -> throwError $ "Unbound variable: " ++ n
       Just t -> return t





-- | Type inference corresponds to the judgment @Γ ⊢ M ⇒ A true@. This throws
-- a Haskell error when trying to infer the type of a bound variable, because
-- all bound variables should be replaced by free variables during this part
-- of type checking.
--
-- The judgment @Γ ⊢ M ⇒ A true@ is defined inductively as follows:
--
-- @
--    Γ ∋ x : A true
--    -------------- variable
--    Γ ⊢ x ⇒ A true
--
--           Δ ∋ n : A
--    ----------------------- definition
--    Γ ⊢ defined[n] ⇒ A true
--
--    Γ ⊢ A ⇐ Type true   Γ ⊢ M ⇐ A true
--    ---------------------------------- annotation
--            Γ ⊢ M : A ⇒ A true
--
--    -------------------- type
--    Γ ⊢ Type ⇒ Type true
--
--    Γ ⊢ A ⇐ Type true   Γ, x : A true ⊢ B ⇐ Type true
--    ------------------------------------------------- function
--              Γ ⊢ (x : A) -> B ⇒ Type true
--    
--    Γ ⊢ M ⇒ (x : A) -> B   Γ ⊢ N ⇐ A true
--    ------------------------------------- application
--            Γ ⊢ M N ⇒ [N/x]B true
--    
--    
--    Σ ∋ c con sig((x0:A0,...,xn:An)B)
--    Γ ⊢ M0 ⇐ A0 true
--    ...
--    Γ ⊢ Mn ⇐ [M0/x0,...]An true
--    ----------------------------------------- constructed data
--    Γ ⊢ con[c](M0;...;Mn) ⇒ [M0/x0,...]B true
--
--    
--    Γ ⊢ mot((x0:A0,...,xm:Am)B) motive
--    Γ ⊢ M0 ⇐ A0 true
--    ...
--    Γ ⊢ Mn ⇐ [M0,x0,...]An true
--    Γ ⊢ Cj clause (x0:A0)...(xm:Am)B
--    ------------------------------------------------------------------- case
--    Γ ⊢ case(M0,...,Mm; mot((x0:A0,...)B); C0,...,Cn) ⇒ [M0/x0,...]B true
-- @

inferify :: Term -> TypeChecker Term

inferify (Var (Free x)) =
  do t <- typeInContext x
     return  t
inferify (Var (Bound _ _)) =
  error "Bound type variables should not be the subject of type checking."
inferify (Var (Meta x)) =
  throwError $ "The metavariable " ++ show x
            ++ " appears in checkable code, when it should not."
inferify (In (Defined x)) =
  do t <- typeInDefinitions x
     return t
inferify (In (Ann m t0)) =
  do let t = instantiate0 t0
     checkify t (NormalTerm (In Type))  -- @Type@ is already normal.
     et <- evaluate (SubstitutedTerm t) -- @t@ can't be changed by checking.
     checkify (instantiate0 m) et
     return $ normTerm et
inferify (In Type)
  = return $ In Type
inferify (In (Fun arg0 sc))
  = do let arg = instantiate0 arg0
       checkify arg (NormalTerm (In Type))
       [n] <- freshRelTo (names sc) context
       extendElab context [(n, arg)]
         $ checkify (instantiate sc [Var (Free n)]) (NormalTerm (In Type))
       return $ In Type
inferify (In (Lam _))
  = throwError "Cannot infer the type of a lambda expression."
inferify (In (App f0 a0))
  = do let f = instantiate0 f0
           a = instantiate0 a0
       t <- inferify f
       subt <- substitute t
       NormalTerm et <- evaluate subt
       case et of
         In (Fun arg sc) -> do
           checkify a (NormalTerm (instantiate0 arg))
             -- @arg@ is already normal in virtue of @et@ being normal.
           return $ instantiate sc [a]
         _ -> throwError $ "Cannot apply non-function: " ++ pretty f
inferify (In (Con c as0)) =
  do let as = map instantiate0 as0
     ConSig tele <- typeInSignature c
     let (args,ret) = instantiateTelescope tele as
         las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     eargs <- mapM (evaluate.SubstitutedTerm) args
       -- @args@ is already substituted, because the consig has no metas, and
       -- neither do the arguments of the constructor.
     zipWithM_ checkify as eargs
     return ret
inferify (In (Case as0 motive cs)) =
  do let as = map instantiate0 as0
     checkifyCaseMotive motive
     let CaseMotive tele = motive
         (args,ret) = instantiateTelescope tele as
         las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ "Motive " ++ pretty motive ++ " expects " ++ show largs
                   ++ " case " ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     eargs <- mapM (evaluate.SubstitutedTerm) args
       -- @args@ is already substituted
     zipWithM_ checkify as eargs
     forM_ cs $ \c -> checkifyClause c motive
     return ret






-- | Type checking corresponds to the judgment @Γ ⊢ M ⇐ A true@.
--
-- The judgment @Γ ⊢ M ⇐ A true@ is defined inductively as follows:
--
-- @
--       Γ, x : A true ⊢ M ⇐ B true
--    -------------------------------- lambda
--    Γ ⊢ lam(x.M) ⇐ (x : A) -> B true
--
--    Γ ⊢ M ⇒ A' true   A = A'
--    ------------------------ direction change
--         Γ ⊢ M ⇐ A true
-- @

checkify :: Term -> NormalTerm -> TypeChecker ()
checkify (In (Lam sc)) (NormalTerm t) =
  do case t of
       In (Fun arg0 sc') -> do
         let arg = instantiate0 arg0
         checkify arg (NormalTerm (In Type))
         [n] <- freshRelTo (names sc) context
         subret <- substitute (instantiate sc' [Var (Free n)])
         eret <- evaluate subret
         extendElab context [(n, arg)]
           $ checkify (instantiate sc [Var (Free n)])
                      eret
       _ -> throwError $ "Cannot check term: " ++ pretty (In (Lam sc)) ++ "\n"
            ++ "Against non-function type: " ++ pretty t
checkify m t =
  do t' <- inferify m
     subt' <- substitute t'
     et' <- evaluate subt'
     unifyHelper t et'
     
     



-- | This corresponds to the judgment @\Gamma \vdash M motive@ which is
-- defined directly in terms of telescopes as as
--
-- @
--    Γ ⊢ T telescope
--    ---------------
--    Γ mot(T) motive
-- @

checkifyCaseMotive :: CaseMotive -> TypeChecker ()
checkifyCaseMotive (CaseMotive tele) = checkifyTelescope tele





-- | This corresponds to the judgment @Γ ⊢ P pattern A yielding M@. The
-- returned term @M@ is the term that corresponds to the pattern, which is
-- necessary for determining if subsequent patterns and the clause body are
-- well typed, since their types can compute over this term. For example,
-- given the motive @(b : Bool) || if b Nat String@, the clause @True -> Zero@
-- should type check, because @True@ is a @Bool@ pattern, and
-- @if True Nat String@ would compute to @Nat@ which @5@ would check against.
--
-- The judgment is defined inductively as follows:
--
-- @
--    ---------------------------------------
--    Γ ⊢ x pattern A yielding x
--
--
--    Σ ∋ c con S
--    Γ ⊢ P0,...,Pn patterns S yielding M0,...,Mn at B'
--    B = B'
--    ----------------------------------------------------------
--    Γ ⊢ con[c](P0;...;Pn) pattern B yielding con[c](M0,...,Mn)
--
--
--              Γ ⊢ M ⇐ A true
--    ----------------------------------
--    Γ ⊢ assert(M) pattern A yielding M
-- @

checkifyPattern :: Pattern
                -> NormalTerm
                -> TypeChecker Term
checkifyPattern (Var (Bound _ _)) _ =
  error "A bound variable should not be the subject of pattern type checking."

checkifyPattern (Var (Free x)) t =
  do t' <- typeInContext x
     unifyHelper t (NormalTerm t')  -- @t'@ is guaranteed to be normal
     return $ Var (Free x)
checkifyPattern (Var (Meta _)) _ =
  error "Metavariables should not be the subject of pattern type checking."
checkifyPattern (In (ConPat c ps)) t =
  do consig <- typeInSignature c
     (ms,ret) <- checkifyPatterns (map instantiate0 ps) consig
     subret <- substitute ret
     eret <- evaluate subret
     unifyHelper eret t
     return $ conH c ms
checkifyPattern (In (AssertionPat m)) t =
  do checkify m t
     return m





-- | This corresponds to the judgment
-- @Γ ⊢ P* patterns S yielding M* at B@ which is defined as follows:
--
-- @
--    Γ ⊢ P0 pattern A0 yielding M0
--    Γ ⊢ P1 pattern [M0/x0]A1 yielding M1
--    Γ ⊢ P2 pattern [M0/x0,M1/x1]A2 yielding M2
--    ...
--    Γ ⊢ Pn pattern [M0/x0,...,Mn-1/xn-1]An yielding Mn
--    --------------------------------------------------
--    Γ ⊢ P0,...,Pn patterns sig((x0:A0)...(xn:An)B)
--          yielding M0,...,Mn at [M0/x0,...,Mn/xn]B
-- @

checkifyPatterns :: [Pattern]
                 -> ConSig
                 -> TypeChecker ([Term], Term)
checkifyPatterns ps0 (ConSig (Telescope ascs bsc)) =
  do ms <- go [] ps0 ascs
     return (ms, instantiate bsc ms)
  where
    go :: [Term] -> [Pattern] -> [Scope TermF] -> TypeChecker [Term]
    go _ [] [] = return []
    go acc (p:ps) (sc:scs) =
      do subt <- substitute (instantiate sc acc)
         et <- evaluate subt
         m <- checkifyPattern p et
         ms <- go (acc ++ [m]) ps scs
         return $ m:ms
    go _ _ _ =
      error $ "The auxiliary function 'go' in 'checkPatterns' should always"
           ++ " have equal number of args for its patterns and scopes. This"
           ++ " branch should never have been reached."





-- | This corresponds to the judgment
-- @Γ ⊢ P* patterns M at B@ which is defined as follows:
--
-- @
--    Γ ⊢ P0 pattern A0 yielding M0
--    Γ ⊢ P1 pattern [M0/x0]A1 yielding M1
--    Γ ⊢ P2 pattern [M0/x0,M1/x1]A2 yielding M2
--    ...
--    Γ ⊢ Pn pattern [M0/x0,...,Mn-1/xn-1]An yielding Mn
--    --------------------------------------------------------------------
--    Γ ⊢ P0,...,Pn patterns mot((x0:A0,...,xn:An)B) at [M0/x0,...,Mn/xn]B
-- @
--
-- The function itself returns an additional set of terms and types
-- accumulated from the patterns for delayed checking.

checkifyPatternsCaseMotive :: [Pattern]
                           -> CaseMotive
                           -> TypeChecker Term
checkifyPatternsCaseMotive ps0 (CaseMotive (Telescope ascs bsc)) =
  do ms <- go [] ps0 ascs
     return $ instantiate bsc ms
  where
    go :: [Term]
       -> [Pattern]
       -> [Scope TermF]
       -> TypeChecker [Term]
    go _ [] [] =
      return []
    go acc (p:ps) (sc:scs) =
      do subt <- substitute (instantiate sc acc)
         et <- evaluate subt
         m <- checkifyPattern p et
         ms <- go (acc ++ [m]) ps scs
         return $ m:ms
    go _ _ _ =
      error $ "The auxiliary function 'go' in 'checkPatternsCaseMotive'"
           ++ " should always have equal number of args for its patterns and"
           ++ " scopes. This branch should never have been reached."





-- | This corresponds to the judgment @Γ ⊢ C clause M@ which is defined as
-- 
-- @
--    Γ ⊢ P0,...,Pn patterns M ⇝ Γ' at B   Γ, Γ' ⊢ N ⇐ B true
--    -------------------------------------------------------
--              Γ ⊢ clause(P0,...,Pn; N) clause M
-- @
--
-- This also handles the checking of delayed assertion patterns.

checkifyClause :: Clause -> CaseMotive -> TypeChecker ()
checkifyClause (Clause pscs sc) mot@(CaseMotive (Telescope ascs _)) =
  do let lps = length pscs
         las = length ascs
     unless (lps == las)
       $ throwError $ "Motive " ++ pretty mot ++ " expects " ++ show las
                   ++ " case " ++ (if las == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
     ns <- freshRelTo (names sc) context
     let xs1 = map (Var . Free) ns
         xs2 = map (Var . Free) ns
     ctx' <- forM ns $ \n ->
               do m <- nextElab nextMeta
                  return (n, Var (Meta m))
     extendElab context ctx' $
       do ret <- checkifyPatternsCaseMotive
                   (map (\psc -> patternInstantiate psc xs1 xs2)
                        pscs)
                   mot
          subret <- substitute ret
          eret <- evaluate subret
          checkify (instantiate sc xs2) eret







-- | This corresponds to the judgment @Γ ⊢ S signature@ which is defined
-- directly in terms of telescopes as
--
-- @
--      Γ ⊢ T telescope
--    --------------------
--    Γ ⊢ sig(T) signature
-- @

checkConSig :: ConSig -> TypeChecker ()
checkConSig (ConSig tele) = checkifyTelescope tele





-- | This corresponds to the judgment @Γ ⊢ T telescope@ which is used
-- to check that a telescope is well formed as a stack of binders. This is
-- defined inductively as
--
-- @
--    Γ ⊢ A0 : Type true
--    ...
--    Γ, x0 : A0, ..., xn-1 : An-1 ⊢ An : Type true
--    Γ, x0 : A0, ..., xn : An ⊢ B : Type true
--    ---------------------------------------------
--    Γ ⊢ (x0:A0)...(xn:An)B telescope
-- @

checkifyTelescope :: Telescope (Scope TermF) -> TypeChecker ()
checkifyTelescope tele@(Telescope _ retsc) =
  do ns <- freshRelTo (names retsc) context
     forM_ (instantiateTelescopeNames tele ns) $ \(ctx', t) ->
       extendElab context ctx'
         $ checkify t (NormalTerm (In Type))





-- | All metavariables have been solved when the next metavar to produces is
-- the number of substitutions we've found.

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (_nextMeta s == MetaVar (length (_substitution s)))
                   $ throwError "Not all metavariables have been solved."





-- | Checking is just checkifying with a requirement that all metas have been
-- solved.

check :: Term -> NormalTerm -> TypeChecker ()
check m t = do checkify m t
               metasSolved





-- | Infering is just inferifying with a requirement that all metas have been
-- solved. The returned type is instantiated with the solutions.
                
infer :: Term -> TypeChecker Term
infer m = do t <- inferify m
             metasSolved
             subt <- substitute t
             NormalTerm et <- evaluate subt
             return et