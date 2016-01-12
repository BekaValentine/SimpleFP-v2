{-# OPTIONS -Wall #-}
{-# LANGUAGE TypeFamilies #-}







-- | A merely-monadic type checker, no unification.

module Simple.Monadic.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Pretty (pretty)
import Utils.Vars
import Simple.Core.ConSig
import Simple.Core.Term
import Simple.Core.Type
import Simple.Monadic.Elaborator

import Control.Monad.Except







-- | We can check that a type constructor exists by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n tycon@

tyconExists :: String -> Elaborator ()
tyconExists n
  = do tycons <- getElab (signature.typeConstructors)
       unless (n `elem` tycons)
         $ throwError $ "Unknown type constructor: " ++ n


-- | We can get the consig of a constructor by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n con S@

typeInSignature :: String -> Elaborator ConSig
typeInSignature n
  = do consigs <- getElab (signature.dataConstructors)
       case lookup n consigs of
         Nothing -> throwError $ "Unknown constructor: " ++ n
         Just t  -> return t


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n : A@

typeInDefinitions :: String -> Elaborator Type
typeInDefinitions x
  = do defs <- getElab definitions
       case lookup x defs of
         Nothing    -> throwError $ "Unknown constant/defined term: " ++ x
         Just (_,t) -> return t


-- | We can get the type of a generated variable by looking in the context.
-- This corresponds to the judgment @Γ ∋ x : A true@

typeInContext :: FreeVar -> Elaborator Type
typeInContext v@(FreeVar n)
  = do ctx <- getElab context
       case lookup v ctx of
         Nothing -> throwError $ "Unbound free variable: " ++ n
         Just t -> return t





-- | Type well-formedness corresponds to the judgment @A type@. This throws a
-- Haskell error if it encounters a variable because there should be no
-- vars in this type checker. That would only be possible for types coming
-- from outside the parser. Same for metavariables.
--
-- The judgment @A type@ is defined inductively as follows:
--
-- @
--    Σ ∋ n tycon
--   -------------
--   TyCon[n] type
--  
--   a type   b type
--   ---------------
--     a -> b type
-- @

isType :: Type -> Elaborator ()
isType (Var _) =
  error "Type variables should not be present in the this type checker."
isType (In (TyCon n)) = tyconExists n
isType (In (Fun a b)) = do isType (instantiate0 a)
                           isType (instantiate0 b)





-- | Type inference corresponds to the judgment @Γ ⊢ M ⇒ A true@. This throws
-- a Haskell error when trying to infer the type of a bound variable, because
-- all bound variables should be replaced by generated variables during this
-- part of type checking.
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

infer :: Term -> Elaborator Type
infer (Var (Bound _ _)) =
  error "A bound variable should never be the subject of type inference."
infer (Var (Free x)) =
  typeInContext x
infer (Var (Meta _ _)) =
  error "Metavariables should not occur in this type checker."
infer (In (Defined n)) =
  typeInDefinitions n
infer (In (Ann m t)) =
  do check (instantiate0 m) t
     return t
infer (In (Lam _)) =
  throwError "Cannot infer the type of a lambda expression."
infer (In (App f a)) =
  do In (Fun arg ret) <- infer (instantiate0 f)
     check (instantiate0 a) (instantiate0 arg)
     return $ instantiate0 ret
infer (In (Con c as)) =
  do ConSig args ret <- typeInSignature c
     let las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ c ++ " expects " ++ show largs ++ " "
                 ++ (if largs == 1 then "arg" else "args")
                 ++ " but was given " ++ show las
     zipWithM_ check (map instantiate0 as) args
     return ret
infer (In (Case ms cs)) =
  do ts <- mapM infer (map instantiate0 ms)
     inferClauses ts cs





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

inferClause :: [Type] -> Clause -> Elaborator Type
inferClause patTys (Clause pscs sc)
  = do let lps = length pscs
       unless (length patTys == lps)
         $ throwError $ "Mismatching number of patterns. Expected "
                     ++ show (length patTys)
                     ++ " but found " ++ show lps
       ns <- freshRelTo (names sc) context
       let xs1 = map (Var . Free) ns
           xs2 = map (Var . Free) ns
       ctx' <- fmap concat
                 $ zipWithM checkPattern
                            (map (\p -> instantiate p xs1) pscs)
                            patTys
       extendElab context ctx'
         $ infer (instantiate sc xs2)





-- | The monadic generalization of 'inferClause', ensuring that there's at
-- least one clause to check, and that all clauses have the same result type.

inferClauses :: [Type] -> [Clause] -> Elaborator Type
inferClauses patTys cs
  = do ts <- mapM (inferClause patTys) cs
       case ts of
         [] -> throwError "Empty clauses."
         t:ts'
           | all (== t) ts' -> return t
           | otherwise ->
               throwError $ "Clauses do not all return the same type:\n"
                         ++ unlines (map pretty ts)





-- | Type checking corresponds to the judgment @Γ ⊢ M ⇐ A true@.
--
-- The judgment @Γ ⊢ M ⇐ A true@ is defined inductively as follows:
--
-- @
--    Γ, x : A true ⊢ M ⇐ B true
--    -------------------------- lambda
--    Γ ⊢ lam(x.M) ⇐ A -> B true
--
--    Γ ⊢ M ⇒ A' true   A = A'
--    ------------------------ direction change
--         Γ ⊢ M ⇐ A true
-- @

check :: Term -> Type -> Elaborator ()
check (In (Lam sc)) (In (Fun arg ret))
  = do [n] <- freshRelTo (names sc) context
       extendElab context [(n, instantiate0 arg)]
         $ check (instantiate sc [Var (Free n)])
                 (instantiate0 ret)
check (In (Lam sc)) t
  = throwError $ "Cannot check term: " ++ pretty (In (Lam sc)) ++ "\n"
              ++ "Against non-function type: " ++ pretty t
check m t
  = do t' <- infer m
       unless (t == t')
         $ throwError $ "Expected term: " ++ pretty m ++ "\n"
                     ++ "To have type: " ++ pretty t ++ "\n"
                     ++ "Instead found type: " ++ pretty t'





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

checkPattern :: Pattern -> Type -> Elaborator Context
checkPattern (Var (Bound _ _)) _
  = error "A bound variable should never be the subject of type checking."
checkPattern (Var (Free x)) t
  = return [(x,t)]
checkPattern (Var (Meta _ _)) _ =
  error "Metavariables should not occur in this type checker."
checkPattern (In (ConPat c ps)) t
  = do ConSig args ret <- typeInSignature c
       let lps = length ps
           largs = length args
       unless (lps == largs && t == ret)
         $ throwError $ c ++ " expects " ++ show largs ++ " "
                   ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show lps
       rss <- zipWithM checkPattern (map instantiate0 ps) args
       return $ concat rss