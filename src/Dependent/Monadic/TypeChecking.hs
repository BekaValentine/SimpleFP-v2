{-# OPTIONS -Wall #-}







-- | A merely-monadic type checker, no unification.

module Dependent.Monadic.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Eval
import Utils.Pretty
import Utils.Telescope
import Utils.Vars
import Dependent.Core.ConSig
import Dependent.Core.Evaluation ()
import Dependent.Core.Term
import Dependent.Monadic.Elaborator
import Dependent.Monadic.Equality ()

import Control.Monad.Except
import Control.Monad.Reader







-- | It's useful to have a way of evaluating without having to constantly get
-- make an environment and run the evaluator manually.

evaluate :: Term -> TypeChecker Term
evaluate m =
  do defs <- getElab definitions
     case runReaderT (eval m) (definitionsToEnvironment defs) of
       Left e   -> throwError e
       Right m' -> return m'


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
--      Γ ⊢ M ⇐ A true
--    ------------------ annotation
--    Γ ⊢ M : A ⇒ A true
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

infer :: Term -> TypeChecker Term
infer (Var (Bound _ _)) =
  error "A bound variable should never be the subject of type inference."
infer (Var (Free x)) =
  typeInContext x
infer (Var (Meta _)) =
  error "Meta variables should not exist in this type checker."
infer (In (Defined x)) =
  typeInDefinitions x
infer (In (Ann m t0)) =
  do let t = instantiate0 t0
     check t (In Type)
     et <- evaluate t
     check (instantiate0 m) et
     return et
infer (In Type) =
  return $ In Type
infer (In (Fun arg0 sc)) =
  do let arg = instantiate0 arg0
     check arg (In Type)
     [n] <- freshRelTo (names sc) context
     extendElab context [(n, arg)]
       $ check (instantiate sc [Var (Free n)]) (In Type)
     return $ In Type
infer (In (Lam _)) =
  throwError "Cannot infer the type of a lambda expression."
infer (In (App f0 a0)) =
  do let f = instantiate0 f0
         a = instantiate0 a0
     t <- infer f
     et <- evaluate t
     case et of
       In (Fun arg sc) -> do
         earg <- evaluate (instantiate0 arg)
         check a earg
         return (instantiate sc [a])
       _ -> throwError $ "Cannot apply a non-function: " ++ pretty f
infer (In (Con c as0)) =
  do let as = map instantiate0 as0
     ConSig tele <- typeInSignature c
     let (args,ret) = instantiateTelescope tele as
         las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     zipWithM_ check as args
     return ret
infer (In (Case as0 motive cs)) =
  do let as = map instantiate0 as0
     checkCaseMotive motive
     let CaseMotive tele = motive
         (args,ret) = instantiateTelescope tele as
         las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ "Motive " ++ pretty motive ++ " expects " ++ show largs
                   ++ " case " ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     zipWithM_ check as args
     forM_ cs $ \c -> checkClause c motive
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

check :: Term -> Term -> TypeChecker ()
check (In (Lam sc)) t =
  do et <- evaluate t
     case et of
       In (Fun arg0 sc') -> do
         let arg = instantiate0 arg0
         check arg (In Type)
         [n] <- freshRelTo (names sc) context
         eret <- evaluate (instantiate sc' [Var (Free n)])
         extendElab context [(n, arg)]
           $ check (instantiate sc [Var (Free n)])
                   eret
       _ -> throwError $ "Cannot check term: " ++ pretty (In (Lam sc)) ++ "\n"
            ++ "Against non-function type: " ++ pretty t
check m t =
  do t' <- infer m
     et <- evaluate t
     et' <- evaluate t'
     unless (et == et')
       $ throwError $ "Needed a " ++ pretty t ++ " but found " ++ pretty t'
                   ++ " when type checking " ++ pretty m





-- | This corresponds to the judgment @\Gamma \vdash M motive@ which is
-- defined directly in terms of telescopes as as
--
-- @
--    Γ ⊢ T telescope
--    ---------------
--    Γ mot(T) motive
-- @

checkCaseMotive :: CaseMotive -> TypeChecker ()
checkCaseMotive (CaseMotive tele) = checkTelescope tele





-- | This corresponds to the judgment @Γ ⊢ P pattern A → Γ' yielding M@. The
-- returned @Γ'@ is the bindings brought brought into scope by the
-- pattern, which we have to return because this type checker doesn't use
-- unification. The returned term @M@ is the term that corresponds to the
-- pattern, which is necessary for determining if subsequent patterns and
-- the clause body are well typed, since their types can compute over this
-- term. For example, given the motive @(b : Bool) || if b Nat String@, the
-- clause @True -> Zero@ should type check, because @True@ is a @Bool@
-- pattern, and @if True Nat String@ would compute to @Nat@ which @5@ would
-- check against.
--
-- The judgment is defined inductively as follows:
--
-- @
--    ---------------------------------------
--    Γ ⊢ x pattern A ⇝ x : A true yielding x
--
--
--    Σ ∋ c con S
--    Γ ⊢ P0,...,Pn patterns S ⇝ Γ0',...,Γn' yielding M0,...,Mn at B'
--    B = B'
--    ------------------------------------------------------------------------
--    Γ ⊢ con[c](P0;...;Pn) pattern B ⇝ Γ0',...,Γn' yielding con[c](M0,...,Mn)
--
--
--                Γ ⊢ M ⇐ A true
--    --------------------------------------
--    Γ ⊢ assert(M) pattern A ⇝ e yielding M
-- @
--
-- The function itself actually returns an additional set of terms and types
-- representing the assertion pattern args inside the pattern, which can't be
-- type checked immediately because the types for their contexts are not known
-- right away. This is because assertion patterns can use variables that are
-- bound syntactically to their right, for example the pattern @Pair .x x@.
-- This can happily check as a pattern for the type @Prod A A@, but at the
-- time that the assertion pattern is checked, the variable @x@ is not in
-- scope. In a type checker with unification, this wouldn't be necessary
-- because all of the variables could be put into scope with metavariables for
-- their types, and they can immediately be checked, possibly unifying the
-- types as needed, regardless of the order inside the pattern.

checkPattern :: Pattern -> Term -> TypeChecker (Context,Term,[(Term,Term)])
checkPattern (Var (Bound _ _)) _ =
  error "A bound variable should not be the subject of pattern type checking."
checkPattern (Var (Free x)) t =
  return ( [(x,t)]
         , Var (Free x)
         , []
         )
checkPattern (Var (Meta _)) _ =
  error "Metavariables should not occur in this type checker."
checkPattern (In (ConPat _ _)) (In Type) =
  throwError "Cannot pattern match on a type."
checkPattern (In (ConPat c ps)) t =
  do consig <- typeInSignature c
     (ctx,ms,ret,delayed) <- checkPatterns (map instantiate0 ps) consig
     eret <- evaluate ret
     et <- evaluate t
     unless (et == eret)
       $ throwError $ "Needed a " ++ pretty et ++ " but found " ++ pretty eret
                   ++ " when type checking the pattern "
                   ++ pretty (In (ConPat c ps))
     return (ctx, conH c ms, delayed)
checkPattern (In (AssertionPat m)) t =
  return ( []
         , m
         , [(m,t)]
         )
  




-- | This corresponds to the judgment
-- @Γ ⊢ P* patterns S ⇝ Γ' yielding M* at B@ which is defined as follows:
--
-- @
--    Γ ⊢ P0 pattern A0 ⇝ Γ0' yielding M0
--    Γ ⊢ P1 pattern [M0/x0]A1 ⇝ Γ1' yielding M1
--    Γ ⊢ P2 pattern [M0/x0,M1/x1]A2 ⇝ Γ2' yielding M2
--    ...
--    Γ ⊢ Pn pattern [M0/x0,...,Mn-1/xn-1]An ⇝ Γn' yielding Mn
--    ------
--    Γ ⊢ P0,...,Pn patterns sig((x0:A0)...(xn:An)B)
--          ⇝ Γ0',...,Γn' yielding M0,...,Mn at [M0/x0,...,Mn/xn]B
-- @
--
-- The function itself returns an additional set of terms and types
-- accumulated from the patterns for delayed checking.

checkPatterns :: [Pattern]
              -> ConSig
              -> TypeChecker (Context,[Term],Term,[(Term,Term)])
checkPatterns ps0 (ConSig (Telescope ascs bsc)) =
  do (ctx, ms, delayed) <- go [] ps0 ascs
     return (ctx, ms, instantiate bsc ms, delayed)
  where
    go :: [Term]
       -> [Pattern]
       -> [Scope TermF]
       -> TypeChecker (Context, [Term], [(Term,Term)])
    go _ [] [] = return ([], [], [])
    go acc (p:ps) (sc:scs) =
      do (ctx, m, delayed) <- checkPattern p (instantiate sc acc)
         (ctx', ms, delayed') <- go (acc ++ [m]) ps scs
         return (ctx ++ ctx', m:ms, delayed ++ delayed')
    go _ _ _ =
      error $ "The auxiliary function 'go' in 'checkPatterns' should always"
           ++ " have equal number of args for its patterns and scopes. This"
           ++ " branch should never have been reached."





-- | This corresponds to the judgment
-- @Γ ⊢ P* patterns M ⇝ Γ' at B@ which is defined as follows:
--
-- @
--    Γ ⊢ P0 pattern A0 ⇝ Γ0' yielding M0
--    Γ ⊢ P1 pattern [M0/x0]A1 ⇝ Γ1' yielding M1
--    Γ ⊢ P2 pattern [M0/x0,M1/x1]A2 ⇝ Γ2' yielding M2
--    ...
--    Γ ⊢ Pn pattern [M0/x0,...,Mn-1/xn-1]An ⇝ Γn' yielding Mn
--    --------------------------------------------------------
--    Γ ⊢ P0,...,Pn patterns mot((x0:A0,...,xn:An)B)
--           ⇝ Γ0',...,Γn' at [M0/x0,...,Mn/xn]B
-- @
--
-- The function itself returns an additional set of terms and types
-- accumulated from the patterns for delayed checking.

checkPatternsCaseMotive :: [Pattern]
                        -> CaseMotive
                        -> TypeChecker (Context,Term,[(Term,Term)])
checkPatternsCaseMotive ps0 (CaseMotive (Telescope ascs bsc)) =
  do (ctx, ms, delayed) <- go [] ps0 ascs
     return (ctx, instantiate bsc ms, delayed)
  where
    go :: [Term]
       -> [Pattern]
       -> [Scope TermF]
       -> TypeChecker (Context, [Term], [(Term,Term)])
    go _ [] [] = return ([], [], [])
    go acc (p:ps) (sc:scs) =
      do (ctx, m, delayed) <- checkPattern p (instantiate sc acc)
         (ctx', ms, delayed') <- go (acc ++ [m]) ps scs
         return (ctx ++ ctx', m:ms, delayed ++ delayed')
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

checkClause :: Clause -> CaseMotive -> TypeChecker ()
checkClause (Clause pscs sc) mot@(CaseMotive (Telescope ascs _)) =
  do let lps = length pscs
         las = length ascs
     unless (lps == las)
       $ throwError $ "Motive " ++ pretty mot ++ " expects " ++ show las
                   ++ " case " ++ (if las == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
     ns <- freshRelTo (names sc) context
     let xs1 = map (Var . Free) ns
         xs2 = map (Var . Free) ns
     (ctx', ret, delayed) <- checkPatternsCaseMotive
                               (map (\psc -> patternInstantiate psc xs1 xs2)
                                    pscs)
                               mot
     forM_ delayed $ \(m,t) -> extendElab context ctx' (check m t)
     eret <- evaluate ret
     extendElab context ctx'
       $ check (instantiate sc xs2) eret





-- | This corresponds to the judgment @Γ ⊢ S signature@ which is defined
-- directly in terms of telescopes as
--
-- @
--      Γ ⊢ T telescope
--    --------------------
--    Γ ⊢ sig(T) signature
-- @

checkConSig :: ConSig -> TypeChecker ()
checkConSig (ConSig tele) = checkTelescope tele





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

checkTelescope :: Telescope (Scope TermF) -> TypeChecker ()
checkTelescope tele@(Telescope _ retsc) =
  do ns <- freshRelTo (names retsc) context
     forM_ (instantiateTelescopeNames tele ns) $ \(ctx', t) ->
       extendElab context ctx'
         $ check t (In Type)