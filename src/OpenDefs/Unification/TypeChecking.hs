{-# OPTIONS -Wall #-}







-- | A unification-based type checker.

module OpenDefs.Unification.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Eval
import Utils.Names
import Utils.Plicity
import Utils.Pretty
import Utils.Unifier
import Utils.Telescope
import Utils.Vars
import OpenDefs.Core.ConSig
import OpenDefs.Core.Evaluation ()
import OpenDefs.Core.Term
import OpenDefs.Unification.Elaborator
import OpenDefs.Unification.Unification ()

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (inits)







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


-- | Another helpful type, used for ensuring that we return elaborated terms
-- from inference and checking.

newtype ElaboratedTerm = ElaboratedTerm { elabTerm :: Term }


-- | We'd like to make sure that unification only happens to normal terms, so
-- we'll define a convenience function we can use.

unifyHelper :: NormalTerm -> NormalTerm -> TypeChecker ()
unifyHelper (NormalTerm x) (NormalTerm y) =
  unify substitution context x y


-- | We can unalias a name. This corresponds to the judgment @L ∋ n alias n'@
-- which is just an lookup on aliases. @n@ here can be either a bare local
-- name such as @foo@ or a dotted name like @Mod.foo@, and @n'@ is an
-- absolute name @Mod.foo@.

unalias :: Name -> TypeChecker (String,String)
unalias (BareLocal n) =
  do als <- getElab aliases
     case lookup (Left n) als of
       Nothing ->
         throwError $ "The symbol " ++ n ++ " is not an alias for any "
                      ++ "module-declared symbol."
       Just p ->
         return p
unalias (DottedLocal m n) =
  do als <- getElab aliases
     case lookup (Right (m,n)) als of
       Nothing ->
         throwError $ "The symbol " ++ m ++ "." ++ n
                      ++ " is not an alias for any "
                      ++ "module-declared symbol."
       Just p ->
         return p
unalias (Absolute m n) =
  return (m,n)


-- | We can get the consig of a constructor by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n ▹ n' con S@. In the presence of
-- aliases, this also requires some amount of elaboration.

typeInSignature :: Name -> Elaborator (Name,ConSig)
typeInSignature n0 =
  do (m,n) <- unalias n0
     consigs <- getElab signature
     case lookup (m,n) consigs of
       Nothing ->
         throwError $ "Unknown constructor: " ++ showName (Absolute m n)
       Just t ->
         return (Absolute m n, t)


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n ▹ n' : A@. In the presence of
-- aliases, this also requires some amount of elaboration.

typeInDefinitions :: Name -> Elaborator (Name,Term)
typeInDefinitions n0 =
  do (m,n) <- unalias n0
     defs <- getElab definitions
     case lookup (m,n) defs of
       Nothing ->
         throwError $ "Unknown constant/defined term: "
                      ++ showName (Absolute m n)
       Just (_,t) ->
         return (Absolute m n, t)


-- | We can get the type of a free variable by looking in the context. This
-- corresponds to the judgment @Γ ∋ x : A true@

typeInContext :: FreeVar -> Elaborator Term
typeInContext v@(FreeVar n) =
  do ctx <- getElab context
     case lookup v ctx of
       Nothing -> throwError $ "Unbound variable: " ++ n
       Just t -> return t





-- | Type inference corresponds to the judgment @Γ ⊢ M ▹ M' ⇒ A true@. This
-- throws a Haskell error when trying to infer the type of a bound variable,
-- because all bound variables should be replaced by free variables during
-- this part of type checking.
--
-- The second term @M'@ in the judgment is the output term that has all
-- implicit arguments elaborated. For instance, application of a function
-- with implicit arguments initially will need to have those arguments
-- inserted. Those arguments are necessary for computation, so we need to
-- have a resulting elaborated term returned by the type checker.
--
-- The judgment @Γ ⊢ M ▹ M' ⇒ A true@ is defined inductively as follows:
--
-- @
--      Γ ∋ x : A true
--    ------------------ variable
--    Γ ⊢ x ▹ x ⇒ A true
--
--               Δ ∋ n ▹ n' : A
--    ------------------------------------ definition
--    Γ ⊢ defined[n] ▹ defined[n'] ⇒ A true
--
--    Γ ⊢ A ▹ A' ⇐ Type true   Γ ⊢ M ▹ M'  ⇐ A' true
--    ---------------------------------------------- annotation
--            Γ ⊢ M : A ▹ M' : A'  ⇒ A' true
--
--    -------------------- type
--    Γ ⊢ Type ▹ Type ⇒ Type true
--
--    Γ ⊢ A ▹ A' ⇐ Type true   Γ, x : A' true ⊢ B ▹ B' ⇐ Type true
--    ------------------------------------------------------------ function
--    Γ ⊢ (x : A) -> B ▹ (x : A') -> B' ⇒ Type true
--    
--    Γ ⊢ M ▹ M' ⇒ S true   Γ ⊢ M' at S applied Plic to N ▹ P ⇒ B true
--    ---------------------------------------------------------------- app
--                  Γ ⊢ app(Plic;M;N) ▹ P ⇒ B true
--    
--    Σ ∋ c ▹ c' sig(Pl*;(A*)B)
--    Γ ⊢ zip(Pl*,A*) at B of M* ▹ M*' ⇒ B'
--    ----------------------------------------- con data
--      Γ ⊢ con[c](M*) ▹ con[c'](M*') ⇒ B' true
--    
--    Γ ⊢ mot((x0:A0,...,xm:Am)B) motive
--    Γ ⊢ M0 ⇐ A0 true
--    ...
--    Γ ⊢ Mn ⇐ [M0,x0,...]An true
--    Γ ⊢ Cj clause (x0:A0)...(xm:Am)B
--    ------------------------------------------------------------------- case
--    Γ ⊢ case(M0,...,Mm; mot((x0:A0,...)B); C0,...,Cn) ⇒ [M0/x0,...]B true
--
--    Γ ⊢ A0 ▹ A0' ⇐ Type true
--    Γ, x0 : A0' true ⊢ A1 ▹ A1' ⇐ Type true
--    ...
--    Γ, x0 : A0' true, ..., xn-1 : An-1' true ⊢ An ▹ An' ⇐ Type true
--    --------------------------------------------------------------- rec
--    Γ ⊢ rec { x0 : A0, ..., xn : An }
--          ▹ rec { x0 : A0', ..., xn : An' } ⇒ Type true
--
--         Γ ⊢ M ▹ M' ⇒ { x0 : A0, ..., xn : An } true
--    ------------------------------------------------------ projection
--    Γ ⊢ M.xi ▹ M'.xi ⇒ [M'.x0/x0, ...,M'.xi-1/xi-1]Ai true
-- @
--
-- This judgment will also happily infer the type of a constructor, because
-- it has similarities to functions in that the "type" (really, signature) is
-- given prior to the arguments. However, unlike functions, this is not
-- guaranteed to work, as constructors in theory should be checked, not
-- inferred. This is a kind of best-effort inferrence, that will sometimes
-- fail in practice (tho the judgment doesn't make this clear) when the
-- constructor in question has implicit arguments that take part in computed
-- indexes of the return type. For instance, the type
--
-- @
--    data Inv (f : Nat -> Nat) (y : Nat) where
--      | MkInv {f : Nat -> Nat} (x : Nat) : Inv f (f x)
--    end
-- @
--
-- This would happily check, for instance @MkInv 3 : Inv (+2) 1@, but to try
-- to infer the type of @MkInv@ requires implicitly fetermining some function
-- @f@, which is obviously not possible, as there could be infinitely many.
-- In other cases, the implicit argument to the constructor may not even be
-- an index of the type, making the inference problem even harder. This
-- function is therefore only for certain use cases, where the constructor is
-- "obviously" inferrable.

inferify :: Term -> TypeChecker (ElaboratedTerm,Term)

inferify (Var (Free x)) =
  do t <- typeInContext x
     return (ElaboratedTerm (Var (Free x)), t)
inferify (Var (Bound _ _)) =
  error "Bound type variables should not be the subject of type checking."
inferify (Var (Meta x)) =
  throwError $ "The metavariable " ++ show x
            ++ " appears in checkable code, when it should not."
inferify (In (Defined x)) =
  do (ex,t) <- typeInDefinitions x
     return (ElaboratedTerm (In (Defined ex)), t)
inferify (In (Ann m t0)) =
  do let t = instantiate0 t0
     ElaboratedTerm elt <- checkify t (NormalTerm (In Type))
     et <- evaluate (SubstitutedTerm elt) -- @t@ can't be changed by checking.
     elm <- checkify (instantiate0 m) et
     return (elm, normTerm et)
inferify (In Type)
  = return $ (ElaboratedTerm (In Type), In Type)
inferify (In (Fun plic arg0 sc))
  = do let arg = instantiate0 arg0
       ElaboratedTerm elarg <- checkify arg (NormalTerm (In Type))
       [x@(FreeVar n)] <- freshRelTo (names sc) context
       ElaboratedTerm elbody <- extendElab context [(x, elarg)]
         $ checkify (instantiate sc [Var (Free x)]) (NormalTerm (In Type))
       let t' = funH plic n elarg elbody
       SubstitutedTerm subt' <- substitute t'
       return (ElaboratedTerm subt', In Type)
inferify (In (Lam _ _))
  = throwError "Cannot infer the type of a lambda expression."
inferify (In (App plic f0 a0))
  = do let f = instantiate0 f0
           a = instantiate0 a0
       (ElaboratedTerm elf,t) <- inferify f
       subt <- substitute t
       NormalTerm et <- evaluate subt
       (app',t') <- inferifyApplication elf et plic a
       SubstitutedTerm subapp' <- substitute app'
       SubstitutedTerm subt' <- substitute t'
       return (ElaboratedTerm subapp', subt')
inferify (In (Con c ms0)) =
  do (ec, ConSig plics (BindingTelescope ascs bsc)) <- typeInSignature c
     let ts = zip plics ascs
         ms = [ (plic, instantiate0 m) | (plic,m) <- ms0 ]
     (ms',b') <- inferifyConArgs ts bsc ms
     let m' = conH ec ms'
     SubstitutedTerm subm' <- substitute m'
     return (ElaboratedTerm subm', b')
inferify (In (Case as0 motive cs)) =
  do let as = map instantiate0 as0
     elmotive <- checkifyCaseMotive motive
     let CaseMotive tele = elmotive
         (args,ret) = instantiateBindingTelescope tele as
         las = length as
         largs = length args
     unless (las == largs)
       $ throwError $ "Motive " ++ pretty motive ++ " expects " ++ show largs
                   ++ " case " ++ (if largs == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     eargs <- mapM (evaluate.SubstitutedTerm) args
       -- @args@ is already substituted
     elas <- zipWithM checkify as eargs
     elcs <- forM cs $ \c -> checkifyClause c elmotive
     let m' = caseH (map elabTerm elas) elmotive elcs
     SubstitutedTerm subm' <- substitute m'
     return (ElaboratedTerm subm', ret)
inferify (In (RecordType fields tele)) =
  do tele' <- checkifyTelescope tele
     return (ElaboratedTerm (In (RecordType fields tele')), In Type)
inferify (In (RecordCon _)) =
  throwError "Cannot infer the type of a record."
inferify (In (RecordProj r x)) =
  do (ElaboratedTerm r',t) <- inferify (instantiate0 r)
     subt <- substitute t
     NormalTerm et <- evaluate subt
     case et of
       In (RecordType fields (Telescope ascs')) ->
         let fieldTable = zip fields (instantiations r' fields ascs')
         in case lookup x fieldTable of
              Nothing ->
                throwError $ "Missing field " ++ x
              Just fieldT ->
                return (ElaboratedTerm (recordProjH r' x), fieldT)
       _ -> throwError $ "Expecting a record type but found "
              ++ pretty et
  where
    
    -- | This just defines all the possible projections of @r'@ using fields
    -- @fs'@, eg. @projections R ["foo","bar","baz"]@ is the terms
    -- @R.foo@, @R.bar@, and @R.baz@.
    
    projections :: Term -> [String] -> [Term]
    projections r' fs' = [ recordProjH r' f' | f' <- fs' ]
    
    -- | This instantiates scopes from a record type at all its possible
    -- fields, so that you get the types for each field. For instance, 
    -- we want to take a record @R : Rec { foo : A, bar : B}@ and extract
    -- @A@ for the type of @R.foo@ and @[R.foo/foo]B@ for the type of @R.bar@.
    
    instantiations :: Term -> [String] -> [Scope TermF] -> [Term]
    instantiations r' fs' ascs' =
      zipWith instantiate ascs' (inits (projections r' fs'))





-- | Because implicit application exists to make certain applications more
-- convenient for the user, we want to be able to apply a function which
-- has some number of implicit arguments first to an explicit argument by
-- inserting however many implicit arguments as necessary. That is, given
-- @M : {x0 : A0} -> ... -> {xn : An} -> (y : B) -> C@ and @N : B@ we want
-- to be able to write @M N@ and have that type check. So we have this helper
-- judgment @Γ ⊢ M at S applied Plic to N ▹ P ⇒ B@ to make 'inferify' easier
-- to define.
--
-- This can be seen as actually not necessary, where the above rules are
-- defined instead purely in terms of just application, since the underlying
-- type theory doesn't have truly implicit application of any sort, but
-- because this is an elaborating type checker, it's clearer if we explain
-- things in terms of this.
--
-- @
--                       Γ ⊢ N ▹ N' ⇐ A true
--    --------------------------------------------------------------
--    Γ ⊢ M at (x : A) -> B applied explicitly to N ▹ M N' ⇒ [N'/x]B
--    
--                       Γ ⊢ N ▹ N' ⇐ A true
--    --------------------------------------------------------------
--    Γ ⊢ M at {x : A} -> B applied implicitly to N ▹ M N' ⇒ [N'/x]B
--    
--     Γ ⊢ M {P} at [P/x]B applied explicitly to N ▹ Q ⇒ C
--    -----------------------------------------------------
--    Γ ⊢ M at {x : A} -> B applied explicitly to N ▹ Q ⇒ C
-- @

inferifyApplication :: Term
                    -> Term
                    -> Plicity
                    -> Term
                    -> TypeChecker (Term,Term)
inferifyApplication f (In (Fun Expl a sc)) Expl m =
  do ElaboratedTerm m' <- checkify m (NormalTerm (instantiate0 a))
     return (appH Expl f m', instantiate sc [m'])
inferifyApplication f (In (Fun Impl a sc)) Impl m =
  do ElaboratedTerm m' <- checkify m (NormalTerm (instantiate0 a))
     return (appH Impl f m', instantiate sc [m'])
inferifyApplication f (In (Fun Expl _ _)) Impl m =
  throwError $ "Mismatching plicities when checking the application "
    ++ pretty (appH Impl f m)
inferifyApplication f (In (Fun Impl _ sc)) Expl m =
  do meta <- nextElab nextMeta
     let f' = appH Impl f (Var (Meta meta))
         t' = instantiate sc [Var (Meta meta)]
     inferifyApplication  f' t' Expl m
inferifyApplication f _ _ _ =
  throwError $ "Cannot apply non-function: " ++ pretty f





-- | As with function application, we can infer the type of a constructor
-- application while simultaneously inserting implicit arguments with the
-- judgment @Γ ⊢ T at B of M* ▹ M*' ⇒ B'@ where @T@  is a sequence of
-- plicity-scope pairs (which we treat as a telescope for readability), and
-- @M*@ and @M*'@ are plicity-term pairs. The judgment is defined as
--
-- @
--    ------------------------
--    Γ ⊢ e at B of e ▹ e ⇒ B
--
--       Γ ⊢ M0 ▹ M0' ⇐ A0   Γ ⊢ [M0'/x0]T at [M0'/x0]B of M* ▹ M*' ⇒ B'
--    ----------------------------------------------------------------------
--    Γ ⊢ (Expl, x0 : A0), T at B of (Expl, M0), M* ▹ (Expl, M0'), M*' ⇒ B'
--
--       Γ ⊢ M0 ▹ M0' ⇐ A0   Γ ⊢ [M0'/x0]T at [M0'/x0]B of M* ▹ M*' ⇒ B'
--    ----------------------------------------------------------------------
--    Γ ⊢ (Impl, x0 : A0), T at B of (Impl, M0), M* ▹ (Impl, M0'), M*' ⇒ B'
--    
--           Γ ⊢ [P/xi]T at [P/xi]B of (Expl,M0), M* ▹ M*' ⇒ B'
--    -----------------------------------------------------------------
--    Γ ⊢ (Impl, xi : Ai), T at B of (Expl,M0), M* ▹ (Impl,P), M*' ⇒ B'
-- @

inferifyConArgs :: [(Plicity,Scope TermF)]
                -> Scope TermF
                -> [(Plicity,Term)]
                -> TypeChecker ([(Plicity,Term)], Term)
inferifyConArgs ascs0 bsc0 ms0 = go [] ascs0 bsc0 ms0
  where
    go :: [(Plicity,Term)]
       -> [(Plicity,Scope TermF)]
       -> Scope TermF
       -> [(Plicity,Term)]
       -> TypeChecker ([(Plicity,Term)], Term)
    go acc [] bsc [] =
      return (acc, instantiate bsc (map snd acc))
    go acc ((Expl,asc):ascs) bsc ((Expl,m):ms) =
      do suba <- substitute (instantiate asc (map snd acc))
         ea <- evaluate suba
         ElaboratedTerm m' <- checkify m ea
         go (acc ++ [(Expl,m')]) ascs bsc ms
    go acc ((Impl,asc):ascs) bsc ((Impl,m):ms) =
      do suba <- substitute (instantiate asc (map snd acc))
         ea <- evaluate suba
         ElaboratedTerm m' <- checkify m ea
         go (acc ++ [(Impl,m')]) ascs bsc ms
    go acc ((Impl,_):ascs) bsc ms =
      do meta <- nextElab nextMeta
         go (acc ++ [(Impl,Var (Meta meta))]) ascs bsc ms
    go _ _ _ _ =
      throwError "Cannot match signature."





-- | Type checking corresponds to the judgment @Γ ⊢ M ▹ M' ⇐ A true@. The
-- implementation inserts implicit lambdas as necessary because implicit
-- arguments exist to make the language more convenient.
--
-- The judgment @Γ ⊢ M ▹ M' ⇐ A true@ is defined inductively as follows:
--
-- @
--              Γ, x : A true ⊢ M ▹ M' ⇐ B true
--    ----------------------------------------------------- lambda
--    Γ ⊢ lam(Pl;x.M) ▹ lam(Pl;x.M') ⇐ Fun(Pl; A; x.B) true
--    
--    Σ ∋ c ▹ c' sig(Pl*;(A*)B)
--    Γ ⊢ zip(Pl*,A*) at B of M* ▹ M*' ⇐ B' true
--    ------------------------------------------ con data
--     Γ ⊢ con[c](M*) ▹ con[c'](M*') ⇐ B' true
--    
--    Γ ⊢ M ▹ M' ⇒ A' true   A = A'
--    ----------------------------- direction change
--         Γ ⊢ M ▹ M' ⇐ A true
--
--    Γ ⊢ M0 ▹ M0' ⇐ A0 true
--    Γ ⊢ M1 ▹ M1' ⇐ [M0'/x0]A1 true
--    ...
--    Γ ⊢ Mn ▹ Mn' ⇐ [M0'/x0,...,Mn-1'/xn-1]An true
--    ----------------------------------------------------------- record
--    Γ ⊢ { x0 = M0, ..., xn : Mn } ▹ { x0 = M0', ..., xn : Mn' }
--           ⇐ rec { x0 : A0, ..., xn : An } true
-- @

checkify :: Term -> NormalTerm -> TypeChecker ElaboratedTerm
checkify (In (Lam plic sc)) (NormalTerm t) =
  do lam' <-
       case (plic,t) of
         (Expl, In (Fun Expl a sc2)) ->  -- \x -> M : (x : A) -> B
           do [v@(FreeVar n)] <- freshRelTo (names sc) context
              let x = Var (Free v)
              ElaboratedTerm m'
                <- extendElab context [(v,instantiate0 a)]
                     $ checkify (instantiate sc [x])
                                (NormalTerm (instantiate sc2 [x]))
              return $ lamH Expl n m'
         (Impl, In (Fun Impl a sc2)) ->  -- \{x} -> M : {x : A} -> B
           do [v@(FreeVar n)] <- freshRelTo (names sc) context
              let x = Var (Free v)
              ElaboratedTerm m'
                <- extendElab context [(v,instantiate0 a)]
                     $ checkify (instantiate sc [x])
                                (NormalTerm (instantiate sc2 [x]))
              return $ lamH Impl n m'
         (Expl, In (Fun Impl a sc2)) ->  --  \x -> M : {y : A} -> B
           do [v@(FreeVar n)] <- freshRelTo (names sc2) context
              let x = Var (Free v)
              ElaboratedTerm m'
                <- extendElab context [(v,instantiate0 a)]
                     $ checkify (In (Lam plic sc))
                                (NormalTerm (instantiate sc2 [x]))
              return $ lamH Impl n m'
         (Impl, In (Fun Expl _ _)) ->  -- \{x} -> M : (y : A) -> B
           throwError $ "Expected an explicit argument but found an implicit "
             ++ "argument when checking " ++ pretty (In (Lam plic sc))
             ++ " matches the signature " ++ pretty t
         _ -> throwError $ "Cannot check term: " ++ pretty (In (Lam plic sc))
                ++ "\nAgainst non-function type: " ++ pretty t
     SubstitutedTerm sublam' <- substitute lam'
     return $ ElaboratedTerm sublam'
checkify (In (Con c ms)) (NormalTerm t) =
  do (ec,ConSig plics (BindingTelescope ascs bsc)) <- typeInSignature c
     elms' <- checkifyConArgs
                (zip plics ascs)
                bsc
                [ (plic, instantiate0 m) | (plic,m) <- ms ]
                t
     let ms' = [ (plic,m') | (plic, ElaboratedTerm m') <- elms' ]
         elm = conH ec ms'
     SubstitutedTerm subelm <- substitute elm
     return $ ElaboratedTerm subelm
checkify (In (RecordCon fields)) (NormalTerm t) =
  case t of
    In (RecordType typeFields (Telescope ascs)) ->
      if length typeFields >= length fields
      then case lookupMany typeFields fields of
        Left missingField ->
          throwError $ "Cannot check the record "
          ++ pretty (In (RecordCon fields)) ++ " against type " ++ pretty t
          ++ " because the record is missing the field " ++ missingField
        Right ms ->
          do ms' <- go [] (map instantiate0 ms) ascs
             return $ ElaboratedTerm (recordConH (zip typeFields ms'))
      else
        throwError $ "Cannot check the record "
          ++ pretty (In (RecordCon fields)) ++ " against type " ++ pretty t
          ++ " because the record has too many fields"
    _ -> throwError $ "Cannot check the record "
           ++ pretty (In (RecordCon fields)) ++ " against type " ++ pretty t
  where
    lookupMany :: Eq k => [k] -> [(k,v)] -> Either k [v]
    lookupMany [] _ = Right []
    lookupMany (k:ks) kvs =
      case lookup k kvs of
        Nothing -> Left k
        Just v ->
          do vs <- lookupMany ks kvs
             return (v:vs)
    
    go :: [Term] -> [Term] -> [Scope TermF] -> TypeChecker [Term]
    go acc [] [] =
      return acc
    go acc (m:ms) (asc:ascs) =
      do suba <- substitute (instantiate asc acc)
         ea <- evaluate suba
         ElaboratedTerm m' <- checkify m ea
         go (acc ++ [m']) ms ascs
    go _ _ _ =
      error $ "This case of 'go' in 'checkify' of a record type should "
           ++ "be unreachable."
checkify m t =
  do (ElaboratedTerm m',t') <- inferify m
     subt' <- substitute t'
     et' <- evaluate subt'
     unifyHelper t et'
     SubstitutedTerm subm' <- substitute m'
     return $ ElaboratedTerm subm'





-- | Ideally, we'd like to check a sequence of args like so:
--
-- @
--    Σ ∋ c sig(Pl0,...,Pln; (x0:A0,...,xn:An)B)
--    Γ ⊢ M0 ▹ M0' ⇐ A0
--    Γ ⊢ M1 ▹ M1' ⇐ [M0'/x0]A1
--    ...
--    Γ ⊢ Mn ▹ Mn' ⇐ [M0'/x0,M1'/x1,...,Mn-1'/xn-1]An
--    --------------------------------------------------------
--    Γ ⊢ con[c]((Pl0,M0);...;(Pln,Mn)) : [M0'/x0,...,Mn',xn]B
-- @
-- 
-- In practice this is tricky, so we have an auxiliary judgment
-- @Γ ⊢ T at B of M* ▹ M*' ⇐ B'@, which is defined inductively as
--
-- @
--    -----------------------
--    Γ ⊢ e at B of e ▹ e ⇐ B
--
--       Γ ⊢ M0 ▹ M0' ⇐ A0   Γ ⊢ [M0'/x0]T at [M0'/x0]B of M* ▹ M*' ⇐ B'
--    ----------------------------------------------------------------------
--    Γ ⊢ (Expl, x0 : A0), T at B of (Expl, M0), M* ▹ (Expl, M0'), M*' ⇐ B'
--
--       Γ ⊢ M0 ▹ M0' ⇐ A0   Γ ⊢ [M0'/x0]T at [M0'/x0]B of M* ▹ M*' ⇐ B'
--    ----------------------------------------------------------------------
--    Γ ⊢ (Impl, x0 : A0), T at B of (Impl, M0), M* ▹ (Impl, M0'), M*' ⇐ B'
--    
--           Γ ⊢ [P/xi]T at [P/xi]B of (Expl,M0), M* ▹ M*' ⇐ B'
--    -----------------------------------------------------------------
--    Γ ⊢ (Impl, xi : Ai), T at B of (Expl,M0), M* ▹ (Impl,P), M*' ⇐ B'
-- @
--
-- This judgment is essentially the same as the inference judgment, except
-- that the implementation here is justified as a bidirectional rule. The
-- implementation, however, is a bit odd, because of how information flows and
-- how equality via evaluation-and-unification works. This arises from two
-- facts. Firstly, constructors can have argument types which compute from
-- indexes. For example
--
-- @
--    data Image (f : Nat -> Type) (x : Nat) where
--      | MkImage {f : Nat -> Type} {x : Nat} (y : f x) : Image f x
--    end
-- @
--
-- The implicit arguments need to therefore be determined by the type checker
-- given the type being checked against. For instance, given
-- @ifZero : Type -> Type -> Nat -> Type@, which behaves as expected, the term
-- @MkImage Unit@ ought to type check at @Image (ifZero Top Bot) Zero@. This
-- means that when type checking the argument @Unit@, we need to check it
-- against @ifZero Top Bot Zero@ which needs to therefore compute to @Top@.
-- Therefore information has to flow from the expected type into the arguments
-- of the constructor, as expected from bidi type checking (lambdas do the
-- same). However there's a second issue, which is that indexes can also be
-- determined by computation, as with the example of @Inv@ from earlier. So
-- information has to in some sense flow in the other direction as well.
-- However, we can avoid this second problem with a cute trick from Conor
-- McBride's paper Elimination with a Motive (learned by McBride from James
-- McKinna), where we extract the computed index into an equation that needs
-- to be solved.
--
-- The overall structure of the algorithm is as follows: for each of the
-- scopes for the constructor argument types, we make a new metavariable. This
-- will eventually be unified with the elaborated argument of that type. We
-- use these to instantiate the scopes, because each term needs to check
-- against a scope and elaborate to some new term, but that scope itself needs
-- to have been instantiated at the fully-elaborated values of previous args.
-- This means we can't use the previous args as-is to instantiate, we need to
-- incrementally instantiate. However, we also need to pass information in
-- from the return type, so these metas are also used to instantiate that.
-- We can then take the return type, swap out its non-meta args (because they
-- might require computation) for purely meta args, and unify. We can now go
-- back, check against the argument types now that we've gotten all the
-- information we can from the return type. This will also involve unifying
-- the returned elabbed arguments with the now-possibly-solved metas that they
-- correspond to. Finally, we can also solve the equations we extracted from
-- the return type.

checkifyConArgs :: [(Plicity,Scope TermF)]
                -> Scope TermF
                -> [(Plicity,Term)]
                -> Term
                -> TypeChecker [(Plicity,ElaboratedTerm)]
checkifyConArgs ascs0 bsc ms0 t =
  do argsToCheck <- accArgsToCheck [] ascs0 ms0
     (eqs,ret') <- case instantiate bsc [ x | (_,_,x,_) <- argsToCheck ] of
                     In (Con c as) ->
                       do (eqs,as') <- swapMetas [ (plic,instantiate0 a)
                                                 | (plic,a) <- as
                                                 ]
                          let ret' = conH c as'
                          return (eqs,ret')
                     ret' -> return ([],ret')
     unifyHelper (NormalTerm ret') (NormalTerm t)
     ms' <- forM argsToCheck $ \(plic,m0,mToElabInto,a) ->
              case m0 of
                Nothing -> 
                  do subMToElabInto <- substitute mToElabInto
                     eMToElabInto <- evaluate subMToElabInto
                     return (plic, ElaboratedTerm (normTerm eMToElabInto))
                Just m ->
                  do subMToElabInto <- substitute mToElabInto
                     eMToElabInto <- evaluate subMToElabInto
                     suba <- substitute a
                     ea <- evaluate suba
                     ElaboratedTerm m' <- checkify m ea
                     SubstitutedTerm subm' <- substitute m'
                     unifyHelper eMToElabInto (NormalTerm subm')
                     return (plic, ElaboratedTerm subm')
     forM_ eqs $ \(l,r) ->
       do subl <- substitute l
          el <- evaluate subl
          subr <- substitute r
          er <- evaluate subr
          unifyHelper el er
     return ms'
  where
    accArgsToCheck :: [(Plicity,Maybe Term,Term,Term)]
                   -> [(Plicity,Scope TermF)]
                   -> [(Plicity,Term)]
                   -> TypeChecker [(Plicity,Maybe Term,Term,Term)]
    accArgsToCheck acc [] [] =
      return acc
    accArgsToCheck acc ((Expl,asc):ascs) ((Expl,m):ms) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Expl, Just m, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ms
    accArgsToCheck acc ((Impl,asc):ascs) ((Impl,m):ms) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Impl, Just m, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ms
    accArgsToCheck acc ((Impl,asc):ascs) ms =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Impl, Nothing, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ms
    accArgsToCheck _ _ _ =
      throwError "Cannot match signature."
    
    swapMetas :: [(Plicity,Term)]
              -> TypeChecker ([(Term,Term)], [(Plicity,Term)])
    swapMetas [] = return ([],[])
    swapMetas ((plic, Var (Meta meta)):ms) =
      do (eqs,ms') <- swapMetas ms
         return (eqs, (plic,Var (Meta meta)):ms')
    swapMetas ((plic,m):ms) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
         (eqs,ms') <- swapMetas ms
         return ((x,m):eqs, (plic,x):ms')
     




-- | This corresponds to the judgment @Γ ⊢ M motive@ which is defined directly
-- in terms of telescopes as as
--
-- @
--    Γ ⊢ T ▹ T' telescope
--    -------------------------
--    Γ ⊢ mot(T) ▹ mot(T') motive
-- @

checkifyCaseMotive :: CaseMotive -> TypeChecker CaseMotive
checkifyCaseMotive (CaseMotive tele) =
  do tele' <- checkifyBindingTelescope tele
     return $ CaseMotive tele'





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
--    ------------------------------
--    Γ ⊢ x ▹ x pattern A yielding x
--
--
--    Σ ∋ c ▹ c' con S
--    Γ ⊢ P0,...,Pn ▹ P0',...,Pn' patterns S yielding M0,...,Mn at B'
--    B = B'
--    ---------------------------------------------------------------
--    Γ ⊢ con[c](P0;...;Pn) ▹ con[c](P0';...;Pn') pattern B
--          yielding con[c'](M0,...,Mn)
--
--
--                 Γ ⊢ M ▹ M' ⇐ A true
--    -----------------------------------------------
--    Γ ⊢ assert(M) ▹ assert(M') pattern A yielding M
-- @

checkifyPattern :: Pattern
                -> NormalTerm
                -> TypeChecker (Pattern,ElaboratedTerm)
checkifyPattern (Var (Bound _ _)) _ =
  error "A bound variable should not be the subject of pattern type checking."
checkifyPattern (Var (Free x)) t =
  do t' <- typeInContext x
     unifyHelper t (NormalTerm t')  -- @t'@ is guaranteed to be normal
     return ( Var (Free x)
            , ElaboratedTerm (Var (Free x))
            )
checkifyPattern (Var (Meta _)) _ =
  error "Metavariables should not be the subject of pattern type checking."
checkifyPattern (In (ConPat c ps)) (NormalTerm t) =
  do (ec,ConSig plics (BindingTelescope ascs bsc)) <- typeInSignature c
     (ps',elms') <-
       checkifyPatterns
         (zip plics ascs)
         bsc
         [ (plic, instantiate0 p) | (plic,p) <- ps ]
         t
     let ms' = [ (plic,m') | (plic, ElaboratedTerm m') <- elms' ]
     return ( conPatH ec ps'
            , ElaboratedTerm (conH ec ms')
            )
checkifyPattern (In (AssertionPat m)) t =
  do ElaboratedTerm m' <- checkify m t
     return ( In (AssertionPat m')
            , ElaboratedTerm m'
            )
checkifyPattern (In MakeMeta) _ =
  do meta <- nextElab nextMeta
     let x = Var (Meta meta)
     return ( In (AssertionPat x)
            , ElaboratedTerm x
            )





-- | This is the pattern version of 'checkifyConArgs', which corresponds to
-- the judgment @Γ ⊢ T at B of P* ▹ P*' pattern B' yielding M*@, which is
-- defined inductively as
--
-- @
--    ----------------------------------------
--    Γ ⊢ e at B of e ▹ e pattern B yielding e
--
--    Γ ⊢ P0 ▹ P0' pattern A0 yielding M0
--    Γ ⊢ [M0'/x0]T at [M0'/x0]B of P* ▹ P*' pattern B' yielding M*
--    ----------------------------------------------------------------
--    Γ ⊢ (Expl, x0 : A0), T at B of (Expl, P0), P* ▹ (Expl, P0'), P*'
--          pattern B' yielding (Expl,M0), M*
--
--    Γ ⊢ P0 ▹ P0' pattern A0 yielding M0
--    Γ ⊢ [M0'/x0]T at [M0'/x0]B of P* ▹ P*' pattern B' yielding M*
--    ----------------------------------------------------------------
--    Γ ⊢ (Impl, x0 : A0), T at B of (Expl, P0), P* ▹ (Impl, P0'), P*'
--          pattern B' yielding (Impl,M0), M*
--    
--    Γ ⊢ [M/xi]T at [M/xi]B of (Expl,P0), P* ▹ P*' pattern B' yielding M*
--    --------------------------------------------------------------------
--    Γ ⊢ (Impl, xi : Ai), T at B of (Expl,P0), P* ▹ (Impl,assert(M)), P*'
--          pattern B' yielding (Impl,M), M*
-- @

checkifyPatterns :: [(Plicity,Scope TermF)]
                 -> Scope TermF
                 -> [(Plicity,Pattern)]
                 -> Term
                 -> TypeChecker ( [(Plicity,Pattern)]
                                , [(Plicity,ElaboratedTerm)]
                                )
checkifyPatterns ascs0 bsc ps0 t =
  do argsToCheck <- accArgsToCheck [] ascs0 ps0
     (eqs,ret') <-
       case instantiate bsc [ x | (_,_,x,_) <- argsToCheck ] of
         In (Con c as) ->
           do (eqs,as') <- swapMetas [ (plic,instantiate0 a)
                                     | (plic,a) <- as
                                     ]
              let ret' = conH c as'
              return (eqs,ret')
         ret' -> return ([],ret')
     unifyHelper (NormalTerm ret') (NormalTerm t)
     psms' <- forM argsToCheck $ \(plic,p0,mToElabInto,a) ->
                case p0 of
                  Nothing ->
                    do subMToElabInto <- substitute mToElabInto
                       em' <- evaluate subMToElabInto
                       return ( (plic, In (AssertionPat (normTerm em')))
                              , (plic, ElaboratedTerm (normTerm em'))
                              )
                  Just p ->
                    do subMToElabInto <- substitute mToElabInto
                       eMToElabInto <- evaluate subMToElabInto
                       suba <- substitute a
                       ea <- evaluate suba
                       (p',ElaboratedTerm m') <- checkifyPattern p ea
                       subm' <- substitute m'
                       em' <- evaluate subm'
                       unifyHelper eMToElabInto em'
                       return ( (plic, p')
                              , (plic, ElaboratedTerm (normTerm em'))
                              )
     forM_ eqs $ \(l,r) ->
       do subl <- substitute l
          el <- evaluate subl
          subr <- substitute r
          er <- evaluate subr
          unifyHelper el er
     return $ unzip psms'
  where
    accArgsToCheck :: [(Plicity,Maybe Pattern,Term,Term)]
                   -> [(Plicity,Scope TermF)]
                   -> [(Plicity,Pattern)]
                   -> TypeChecker [(Plicity,Maybe Pattern,Term,Term)]
    accArgsToCheck acc [] [] =
      return acc
    accArgsToCheck acc ((Expl,asc):ascs) ((Expl,p):ps) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Expl, Just p, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ps
    accArgsToCheck acc ((Impl,asc):ascs) ((Impl,p):ps) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Impl, Just p, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ps
    accArgsToCheck acc ((Impl,asc):ascs) ps =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
             xs = [ x' | (_,_,x',_) <- acc ]
             newSuspension = (Impl, Nothing, x, instantiate asc xs)
         accArgsToCheck
           (acc ++ [newSuspension])
           ascs
           ps
    accArgsToCheck _ _ _ =
      throwError "Cannot match signature."
    
    swapMetas :: [(Plicity,Term)]
              -> TypeChecker ([(Term,Term)], [(Plicity,Term)])
    swapMetas [] = return ([],[])
    swapMetas ((plic, Var (Meta meta)):ms) =
      do (eqs,ms') <- swapMetas ms
         return (eqs, (plic,Var (Meta meta)):ms')
    swapMetas ((plic,m):ms) =
      do meta <- nextElab nextMeta
         let x = Var (Meta meta)
         (eqs,ms') <- swapMetas ms
         return ((x,m):eqs, (plic,x):ms')





-- | This corresponds to the judgment
-- @Γ ⊢ P* ▹ P*' patterns M at B@ which is defined as follows:
--
-- @
--    Γ ⊢ P0 ▹ P0' pattern A0 yielding M0
--    Γ ⊢ P1 ▹ P1' pattern [M0/x0]A1 yielding M1
--    Γ ⊢ P2 ▹ P2' pattern [M0/x0,M1/x1]A2 yielding M2
--    ...
--    Γ ⊢ Pn ▹ Pn' pattern [M0/x0,...,Mn-1/xn-1]An yielding Mn
--    --------------------------------------------------------------------
--    Γ ⊢ P0,...,Pn ▹ P0',...,Pn' patterns mot((x0:A0,...,xn:An)B)
--          at [M0/x0,...,Mn/xn]B
-- @

checkifyPatternsCaseMotive :: [Pattern]
                           -> CaseMotive
                           -> TypeChecker ([Pattern], ElaboratedTerm)
checkifyPatternsCaseMotive ps0 (CaseMotive (BindingTelescope ascs bsc)) =
  do (ps',ms') <- go [] ps0 ascs
     return (ps', ElaboratedTerm (instantiate bsc ms'))
  where
    go :: [Term]
       -> [Pattern]
       -> [Scope TermF]
       -> TypeChecker ([Pattern],[Term])
    go _ [] [] =
      return ([],[])
    go acc (p:ps) (sc:scs) =
      do subt <- substitute (instantiate sc acc)
         et <- evaluate subt
         (p',ElaboratedTerm m') <- checkifyPattern p et
         (ps',ms') <- go (acc ++ [m']) ps scs
         return (p':ps', m':ms')
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

checkifyClause :: Clause -> CaseMotive -> TypeChecker Clause
checkifyClause (Clause pscs sc) mot@(CaseMotive (BindingTelescope ascs _)) =
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
       do (ps',ElaboratedTerm ret) <-
            checkifyPatternsCaseMotive
              (map (\psc -> patternInstantiate psc xs1 xs2)
                   pscs)
              mot
          subret <- substitute ret
          eret <- evaluate subret
          ElaboratedTerm b' <- checkify (instantiate sc xs2) eret
          return $ clauseH [ n | FreeVar n <- ns ] ps' b'





-- | This corresponds to the judgment @Γ ⊢ S signature@ which is defined
-- directly in terms of telescopes as
--
-- @
--            Γ ⊢ T ▹ T' telescope
--    --------------------------------------
--    Γ ⊢ sig(Pl*;T) ▹ sig(Pl*;T') signature
-- @

checkifyConSig :: ConSig -> TypeChecker ConSig
checkifyConSig (ConSig plics tele) =
  do tele' <- checkifyBindingTelescope tele
     return $ ConSig plics tele'





-- | This corresponds to the judgment @Γ ⊢ T telescope@ which is used
-- to check that a telescope is well formed as a stack of binders. This is
-- defined inductively as
--
-- @
--    Γ ⊢ A0 ▹ A0' : Type true
--    ...
--    Γ, x0 : A0', ..., xn-1 : An-1' ⊢ An ▹ An' : Type true
--    -----------------------------------------------------
--    Γ ⊢ x0:A0,...,xn:An ▹ x0:A0',...,xn:An' telescope
-- @

checkifyTelescope :: Telescope (Scope TermF)
                  -> TypeChecker (Telescope (Scope TermF))
checkifyTelescope (Telescope ascs) =
  do ns <- freshRelTo (names (last ascs)) context
     as' <- go ns [] ascs
     let tele' = telescopeH [ n | FreeVar n <- ns ] as'
     return $ tele'
  where
    go :: [FreeVar] -> [Term] -> [Scope TermF] -> TypeChecker [Term]
    go _ _ [] =
      return []
    go vars acc (sc:scs) =
      do let ctx' = zip vars acc
             xs = [ Var (Free x) | x <- take (length (names sc)) vars ]
         ElaboratedTerm a' <-
           extendElab context ctx'
             $ checkify (instantiate sc xs) (NormalTerm (In Type))
         as' <- go vars (acc ++ [a']) scs
         return $ a':as'





-- | This corresponds to the judgment @Γ ⊢ T btelescope@ which is used
-- to check that a telescope is well formed as a stack of binders. This is
-- defined inductively as
--
-- @
--    Γ ⊢ A0 ▹ A0' : Type true
--    ...
--    Γ, x0 : A0', ..., xn-1 : An-1' ⊢ An ▹ An' : Type true
--    Γ, x0 : A0', ..., xn : An' ⊢ B ▹ B' : Type true
--    -----------------------------------------------------
--    Γ ⊢ (x0:A0,...,xn:An)B ▹ (x0:A0',...,xn:An')B' telescope
-- @

checkifyBindingTelescope :: BindingTelescope (Scope TermF)
                         -> TypeChecker (BindingTelescope (Scope TermF))
checkifyBindingTelescope (BindingTelescope ascs bsc) =
  do ns <- freshRelTo (names bsc) context
     asb' <- go ns [] (ascs ++ [bsc])
     let as' = init asb'
         b' = last asb'
     
     let tele' = bindingTelescopeH [ n | FreeVar n <- ns ] as' b'
     return $ tele'
  where
    go :: [FreeVar] -> [Term] -> [Scope TermF] -> TypeChecker [Term]
    go _ _ [] =
      return []
    go vars acc (sc:scs) =
      do let ctx' = zip vars acc
             xs = [ Var (Free x) | x <- take (length (names sc)) vars ]
         ElaboratedTerm a' <-
           extendElab context ctx'
             $ checkify (instantiate sc xs) (NormalTerm (In Type))
         as' <- go vars (acc ++ [a']) scs
         return $ a':as'





-- | All metavariables have been solved when the next metavar to produces is
-- the number of substitutions we've found.

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (_nextMeta s == MetaVar (length (_substitution s)))
                   $ throwError "Not all metavariables have been solved."





-- | Checking is just checkifying with a requirement that all metas have been
-- solved.

check :: Term -> NormalTerm -> TypeChecker Term
check m t = do ElaboratedTerm m' <- checkify m t
               SubstitutedTerm subm' <- substitute m'
               metasSolved
               return subm'





-- | Infering is just inferifying with a requirement that all metas have been
-- solved. The returned type is instantiated with the solutions.
                
infer :: Term -> TypeChecker (Term,Term)
infer m = do (ElaboratedTerm m', t) <- inferify m
             metasSolved
             subt <- substitute t
             NormalTerm et <- evaluate subt
             SubstitutedTerm subm' <- substitute m'
             return (subm',et)