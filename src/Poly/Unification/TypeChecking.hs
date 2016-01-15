{-# OPTIONS -Wall #-}







-- | A unification-based type checker.

module Poly.Unification.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Pretty
import Utils.Unifier
import Utils.Vars
import Poly.Core.ConSig
import Poly.Core.Term
import Poly.Core.Type
import Poly.Unification.Elaborator
import Poly.Unification.Unification ()

import Control.Monad.Except
import Control.Monad.State







-- | We can check that a type constructor exists by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n tycon@

tyconExists :: String -> TypeChecker TyConSig
tyconExists n =
  do tycons <- getElab (signature.typeConstructors)
     case lookup n tycons of
       Nothing -> throwError $ "Unknown type constructor: " ++ n
       Just sig -> return sig


-- | We can get the consig of a constructor by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n con S@

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n =
  do consigs <- getElab (signature.dataConstructors)
     case lookup n consigs of
       Nothing -> throwError $ "Unknown constructor: " ++ n
       Just t  -> return t


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n : A@

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions n =
  do defs <- getElab definitions
     case lookup n defs of
       Nothing -> throwError $ "Unknown constant/defined term: " ++ n
       Just (_,t) -> return t


-- | We can get the type of a generated variable by looking in the context.
-- This corresponds to the judgment @Γ ∋ x : A true@

typeInContext :: FreeVar -> TypeChecker Type
typeInContext x@(FreeVar n) =
  do ctx <- getElab context
     case lookup x ctx of
       Nothing -> throwError $ "Unbound variable: " ++ n
       Just t -> return t


-- | We can check if a type variable is in scope. This corresponds to the
-- judgment @Γ ∋ a type@

tyVarExists :: FreeVar -> TypeChecker ()
tyVarExists x@(FreeVar n) =
  do tyVarCtx <- getElab tyVarContext
     unless (x `elem` tyVarCtx)
       $ throwError $ "Unbound type variable: " ++ n





-- | Type well-formedness corresponds to the judgment @A type@. This throws a
-- Haskell error if it encounters a variable because there should be no
-- vars in this type checker. That would only be possible for types coming
-- from outside the parser. Same for metavariables.
--
-- The judgment @Γ ⊢ A type@ is defined inductively as follows:
--
-- @
--      Σ ∋ n tycon
--   -----------------
--   Γ ⊢ TyCon[n] type
--
--   Γ ∋ a type
--   ----------
--   Γ ⊢ a type
--  
--   Γ ⊢ a type   Γ ⊢ b type
--   -----------------------
--       Γ ⊢ a -> b type
--
--    Γ, a type ⊢ b type
--   --------------------
--   Γ ⊢ forall a. b type
-- @

isType :: Type -> TypeChecker ()
isType (Var (Free x)) =
  tyVarExists x
isType (Var (Bound _ _)) =
  error "Bound type variables should not be the subject of type checking."
isType (Var (Meta _)) =
  error "Metavariables should not be the subject of type checking."
isType (In (TyCon c as)) =
  do TyConSig ar <- tyconExists c
     let las = length as
     unless (ar == las)
       $ throwError $ c ++ " expects " ++ show ar ++ " "
                   ++ (if ar == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     mapM_ (isType.instantiate0) as
isType (In (Fun a b)) =
  do isType (instantiate0 a)
     isType (instantiate0 b)
isType (In (Forall sc)) =
  do ns <- freshRelTo (names sc) context
     let xs = map (Var . Free) ns
     extendElab tyVarContext ns
       $ isType (instantiate sc xs)





-- | We can instantiate the argument and return types for a constructor
-- signature with variables.

instantiateParams :: [Scope TypeF] -> Scope TypeF -> TypeChecker ([Type],Type)
instantiateParams argscs retsc =
  do metas <- replicateM
               (length (names retsc))
               (nextElab nextMeta)
     let ms = map (Var . Meta) metas
     return ( map (\sc -> instantiate sc ms) argscs
            , instantiate retsc ms
            )





-- | We can instantiate a universally quantified type with metavariables
-- eliminating all the initial quantifiers. For example, the type
-- @forall a b. (a -> b) -> a@ would become @(?0 -> ?1) -> ?0@, while the type
-- @forall a. (forall b. a -> b) -> a@ would become
-- @(forall b. ?0 -> b) -> ?0@ and the type @A -> forall b. A -> b@ would be
-- unchanged.

instantiateQuantifiers :: Type -> TypeChecker Type
instantiateQuantifiers (In (Forall sc)) =
  do meta <- nextElab nextMeta
     let m = Var (Meta meta)
     instantiateQuantifiers (instantiate sc [m])
instantiateQuantifiers t = return t





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
--    Γ ⊢ M ⇒ A -> B   Γ ⊢ N ⇐ A
--    -------------------------- application
--           Γ ⊢ M N ⇒ B
--
--    Σ ∋ c con (A0,...,An)B   Γ ⊢ Mi ⇐ Ai true
--    ----------------------------------------- constructed data
--         Γ ⊢ con[c](M0;...;Mn) ⇒ B true
--
--    Γ ⊢ Mi ⇒ Ai true   Γ ⊢ Cj : A0,...,Am clause B
--    ---------------------------------------------- case
--       Γ ⊢ case(M0,...,Mm; C0,...,Cn) ⇒ B true
-- @

inferify :: Term -> TypeChecker Type
inferify (Var (Bound _ _)) =
  error "A bound variable should never be the subject of type inference."
inferify (Var (Free n)) =
  typeInContext n
inferify (Var (Meta _)) =
  error "Metavariables should not be the subject of type inference."
inferify (In (Defined x)) =
  typeInDefinitions x
inferify (In (Ann m t)) =
  do isType t
     checkify (instantiate0 m) t
     subs <- getElab substitution
     return $ substMetas subs t
inferify (In (Lam sc)) =
  do [n] <- freshRelTo (names sc) context
     meta <- nextElab nextMeta
     let arg = Var (Meta meta)
     ret <- extendElab context [(n, arg)]
              $ inferify (instantiate sc [Var (Free n)])
     subs <- getElab substitution
     return $ funH (substMetas subs arg) ret
inferify (In (App f a)) =
  do t <- inferify (instantiate0 f)
     t' <- instantiateQuantifiers t
     case t' of
       In (Fun arg ret) -> do
         checkify (instantiate0 a) (instantiate0 arg)
         subs <- getElab substitution
         return $ substMetas subs (instantiate0 ret)
       _ -> throwError $ "Expected a function type when checking"
                      ++ " the expression: " ++ pretty (instantiate0 f)
                      ++ "\nbut instead found: " ++ pretty t'
inferify (In (Con c as)) =
  do ConSig argscs retsc <- typeInSignature c
     (args',ret') <- instantiateParams argscs retsc
     let las = length as
         largs' = length args'
     unless (las == largs')
       $ throwError $ c ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show las
     checkifyMulti (map instantiate0 as) args'
     subs <- getElab substitution
     return $ substMetas subs ret'
inferify (In (Case ms cs)) =
  do ts <- mapM (inferify.instantiate0) ms
     inferifyClauses ts cs





-- | Type inference for clauses corresponds to the judgment
-- @Γ ⊢ C : A* clause B@ where @A*@ is an input list of types and @B@ is an
-- output type.
--
-- The judgment @Γ ⊢ C : A* clause B@ is defined as follows:
--
-- @
--    m = n   Pi pattern Ai ⇝ Γ'   Γ, Γ' ⊢ M ⇐ B true
--    -----------------------------------------------
--      Γ ⊢ cls(P0,...,Pm; M) : A0,...,An clause B
-- @

inferifyClause :: [Type] -> Clause -> TypeChecker Type
inferifyClause patTys (Clause pscs sc) =
  do let lps = length pscs
     unless (length patTys == lps)
       $ throwError $ "Mismatching number of patterns. Expected "
                   ++ show (length patTys)
                   ++ " but found " ++ show lps
     ns <- freshRelTo (names sc) context
     let xs1 = map (Var . Free) ns
         xs2 = map (Var . Free) ns
     ctx' <- forM ns $ \n -> do
               m <- nextElab nextMeta
               return (n,Var (Meta m))
     extendElab context ctx' $ do
       zipWithM_ checkifyPattern
                 (map (\psc -> instantiate psc xs1) pscs)
                 patTys
       inferify (instantiate sc xs2)





-- | The monadic generalization of 'inferClause', ensuring that there's at
-- least one clause to check, and that all clauses have the same result type.

inferifyClauses :: [Type] -> [Clause] -> TypeChecker Type
inferifyClauses patTys cs =
  do ts <- mapM (inferifyClause patTys) cs
     case ts of
       [] -> throwError "Empty clauses."
       t:ts' -> do
         catchError (mapM_ (unify substitution context t) ts') $ \e ->
           throwError $ "Clauses do not all return the same type:\n"
                     ++ unlines (map pretty ts) ++ "\n"
                     ++ "Unification failed with error: " ++ e
         subs <- getElab substitution
         return (substMetas subs t)





-- | Type checking corresponds to the judgment @Γ ⊢ M ⇐ A true@.
--
-- The judgment @Γ ⊢ M ⇐ A true@ is defined inductively as follows:
--
-- @
--     Γ, a type ⊢ M ⇐ B true
--    ------------------------ forall
--    Γ ⊢ M ⇐ forall a. B true
--
--    Γ, x : A true ⊢ M ⇐ B true
--    -------------------------- lambda
--    Γ ⊢ lam(x.M) ⇐ A -> B true
--
--    Γ ⊢ M ⇒ A' true   A = A'
--    ------------------------ direction change
--         Γ ⊢ M ⇐ A true
-- @

checkify :: Term -> Type -> TypeChecker ()
checkify m (In (Forall sc)) =
  do [n] <- freshRelTo (names sc) context
     extendElab tyVarContext [n]
       $ checkify m (instantiate sc [Var (Free n)])
checkify (In (Lam sc)) (In (Fun arg ret)) =
  do [n] <- freshRelTo (names sc) context
     extendElab context [(n, instantiate0 arg)]
       $ checkify
           (instantiate sc [Var (Free n)])
           (instantiate0 ret)
checkify (In (Lam sc)) t =
  throwError $ "Cannot check term: " ++ pretty (In (Lam sc)) ++ "\n"
            ++ "Against non-function type: " ++ pretty t
checkify m t =
  do t' <- inferify m
     equivQuantifiers t' t





-- | Checkifying a sequence of terms involves chaining substitutions
-- appropriately. This doesn't correspond to a particular judgment so much
-- as a by product of the need to explicitly propagate the effects of
-- unification.

checkifyMulti :: [Term] -> [Type] -> TypeChecker ()
checkifyMulti [] [] = return ()
checkifyMulti (m:ms) (t:ts) =
  do subs <- getElab substitution
     checkify m (substMetas subs t)
     checkifyMulti ms ts
checkifyMulti _ _ =
  throwError "Mismatched constructor signature lengths."






-- | This function checks if the first type can be found to be equivalent to
-- the second by instantiation of its quantifiers. This corresponds to the
-- subtyping judgment @Γ ⊢ S <: T@ which is defined inductively as:
--
-- @
--     Γ, a type ⊢ S <: T
--    --------------------
--    Γ ⊢ S <: forall a. T
--
--      Γ ⊢ [A/a]S <: T
--    --------------------
--    Γ ⊢ forall a. S <: T
--
--    Γ ⊢ A' <: A   Γ ⊢ B <: B'
--    -------------------------
--     Γ ⊢ A -> B <: A' -> B'
--
--    ----------
--    Γ ⊢ A <: A
-- @

equivQuantifiers :: Type -> Type -> TypeChecker ()
equivQuantifiers t (In (Forall sc')) =
  do [n] <- freshRelTo (names sc') context
     equivQuantifiers t (instantiate sc' [Var (Free n)])
equivQuantifiers (In (Forall sc)) t' =
  do meta <- nextElab nextMeta
     let x2 = Var (Meta meta)
     equivQuantifiers (instantiate sc [x2]) t'
equivQuantifiers (In (Fun arg ret)) (In (Fun arg' ret')) =
  do equivQuantifiers (instantiate0 arg') (instantiate0 arg)
     equivQuantifiers (instantiate0 ret) (instantiate0 ret')
equivQuantifiers t t' =
  unify substitution context t t'





-- | Type checking for patterns corresponds to the judgment @P pattern A ⇝ Γ@,
-- where @Γ@ is an output context.
--
-- The judgment @P pattern A ⇝ Γ@ is defined inductively as follows:
--
-- @
--    ------------------------
--    x pattern A ⇝ x : A true
--
--    Σ ∋ c con (A0,...,An)B   Pi pattern Ai ⇝ Γi
--    -------------------------------------------
--      con[c](P0;...;Pn) pattern B ⇝ Γ0,...,Γn
-- @

checkifyPattern :: Pattern -> Type -> TypeChecker ()
checkifyPattern (Var (Bound _ _)) _ =
  error "A bound variable should not be the subject of pattern type checking."
checkifyPattern (Var (Meta _)) _ =
  error "Metavariables should not be the subject of type checking."
checkifyPattern (Var (Free n)) t =
  do t' <- typeInContext n
     unify substitution context t t'
checkifyPattern (In (ConPat c ps)) t =
  do ConSig argscs retsc <- typeInSignature c
     (args',ret') <- instantiateParams argscs retsc
     let lps = length ps
         largs' = length args'
     unless (lps == largs')
       $ throwError $ c ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show lps
     unify substitution context t ret'
     subs <- getElab substitution
     zipWithM_
       checkifyPattern
       (map instantiate0 ps)
       (map (substMetas subs) args')





-- | Type checking of constructor signatures corresponds to the judgment
-- @Γ ⊢ Γ'.(A0;...;An)B consig@ which is defined as
--
-- @
--    Γ, Γ' ⊢ Ai type   Γ, Γ' ⊢ B type
--    --------------------------------
--          Γ ⊢ Γ'.(A0;...;An)B
-- @
--
-- Because of the ABT representation, however, the scope is pushed down inside
-- the 'ConSig' constructor, onto its arguments.

checkifyConSig :: ConSig -> TypeChecker ()
checkifyConSig (ConSig argscs retsc) =
  do ns <- freshRelTo (names retsc) context
     let xs = map (Var . Free) ns
     extendElab tyVarContext ns $ do
       forM_ argscs $ \sc -> isType (instantiate sc xs)
       isType (instantiate retsc xs)





-- | All metavariables have been solved when the next metavar to produces is
-- the number of substitutions we've found.

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (_nextMeta s == MetaVar (length (_substitution s)))
                   $ throwError "Not all metavariables have been solved."





-- | Checking is just checkifying with a requirement that all metas have been
-- solved.

check :: Term -> Type -> TypeChecker ()
check m t = do checkify m t
               metasSolved





-- | Infering is just inferifying with a requirement that all metas have been
-- solved. The returned type is instantiated with the solutions.

infer :: Term -> TypeChecker Type
infer m = do t <- inferify m
             metasSolved
             subs <- getElab substitution
             return $ substMetas subs t