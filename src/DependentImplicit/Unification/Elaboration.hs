{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed.

module DependentImplicit.Unification.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Plicity
import Utils.Pretty
import Utils.Telescope
import Utils.Vars
import DependentImplicit.Core.ConSig
import DependentImplicit.Core.Program
import DependentImplicit.Core.Term
import DependentImplicit.Unification.Elaborator
import DependentImplicit.Unification.TypeChecking

import Control.Monad
import Control.Monad.Except
import Data.List (inits)







-- | We can add a new defined value declaration given a name, term, and type.

addDeclaration :: String -> Term -> Term -> Elaborator ()
addDeclaration n def ty = addElab definitions [(n,(def,ty))]


-- | We can add a new constructor by giving a name and a signature.

addConstructor :: String -> ConSig -> Elaborator ()
addConstructor c consig = addElab signature [(c,consig)]





-- | Elaborating a term declaration takes one of two forms, depending on what
-- kind of declaration is being elaborated. A definition of the form
-- @let f : A = M end@ is elaborated directly, while a definition of the form
-- @let f : A where f x y z = M end@ is first transformed into the former
-- type of declaration, and then elaborated.
--
-- This corresponds to the elaboration judgment @Σ ⊢ let x : A = M end def⇝ Δ@
-- which is defined as
--
-- @
--    Δ # x   ⊢ A ▹ A' ⇐ Type true   x : A' true ⊢ M ▹ M'  ⇐ A' true
--    --------------------------------------------------------------
--           Δ ⊢ let x : A = M end def⇝ Δ, x = M' : A' true
-- @
--
-- where @Δ # x@ means that @x@ is not defined in @Δ@.

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty0 def0) =
  do let ty = freeToDefined (In . Defined) ty0
         def = freeToDefined (In . Defined) def0
     when' (typeInDefinitions n)
         $ throwError ("Term already defined: " ++ n)
     elty <- check ty (NormalTerm (In Type))
     ety <- evaluate (SubstitutedTerm elty) -- @ty@ has no metas to substitute.
     eldef <- extendElab definitions [(n,(def,normTerm ety))]
                $ check def ety
     addDeclaration n eldef (normTerm ety)
elabTermDecl (WhereDeclaration n ty preclauses) =
  case preclauses of
    [] -> throwError "Cannot create an empty let-where definition."
    [(plics,(xs,ps,b))] | all isVarPat ps ->
      elabTermDecl
        (TermDeclaration
           n
           ty
           (helperFold (uncurry lamH) (zip plics xs) b))
    (_,(_,ps0,_)):_ ->
      do let lps0 = length ps0
         unless (all (\(_,(_,ps,_)) -> length ps == lps0) preclauses)
           $ throwError $ "Mismatching number of patterns in different "
                       ++ "clauses of a pattern matching function."
         let (plics:plicss) = map fst preclauses
         unless (all (plics==) plicss)
           $ throwError $ "Mismatching plicities in different clauses of a "
                       ++ "pattern matching function"
         case truePlicities plics ty of
           Nothing ->
             throwError $ "Cannot build a case expression motive from the "
                       ++ "type " ++ pretty ty
           Just truePlics ->
             do let mot = motiveAux (length truePlics) ty
                    clauses = [ clauseH xs (truePatterns truePlics ps) b
                              | (_,(xs,ps,b)) <- preclauses
                              ]
                    xs0 = [ "x" ++ show i | i <- [0..length ps0-1] ]
                    plicsForLambdas = map (either id id) truePlics
                elabTermDecl
                  (TermDeclaration
                     n
                     ty
                     (helperFold
                        (uncurry lamH)
                        (zip plicsForLambdas xs0)
                        (caseH (map (Var . Free . FreeVar) xs0) mot clauses)))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False
    
    truePlicities :: [Plicity] -> Term -> Maybe [Either Plicity Plicity]
    truePlicities [] _ = Just []
    truePlicities (Expl:plics) (In (Fun Expl _ sc)) =
      do rest <- truePlicities plics (body sc)
         return $ Right Expl : rest
    truePlicities (Impl:plics) (In (Fun Impl _ sc)) =
      do rest <- truePlicities plics (body sc)
         return $ Right Impl : rest
    truePlicities (Expl:plics) (In (Fun Impl _ sc)) =
      do rest <- truePlicities (Expl : plics) (body sc)
         return $ Left Impl : rest
    truePlicities (Impl:_) (In (Fun Expl _ _)) = Nothing
    truePlicities _ _ =
      error "This case of 'truePlicities' should never have been reached."
    
    motiveAux :: Int -> Term -> CaseMotive
    motiveAux i0 t0 =
      let (ns,asb) = go i0 t0
          scs = zipWith scope (inits ns) asb
          ascs = init scs
          bsc = last scs
      in CaseMotive (Telescope ascs bsc)
      where
        go :: Int -> Term -> ([String],[Term])
        go 0 b = ([],[b])
        go i (In (Fun _ a sc)) =
          let ([x],t) = descope sc
              (xs,as) = go (i-1) t
          in (x:xs, instantiate0 a:as)
        go _ _ =
          error $ "This case of 'go' in 'motiveAux' should never have been"
               ++ " reached."
    
    truePatterns :: [Either Plicity Plicity] -> [Pattern] -> [Pattern]
    truePatterns [] [] = []
    truePatterns (Right _:plics) (p:ps) =
      p : truePatterns plics ps
    truePatterns (Left _:plics) ps =
      In MakeMeta : truePatterns plics ps
    truePatterns _ _ =
      error "This case of 'truePatterns' should never have been reached."





-- | Elaboration of a constructor in this variant is a relatively simple
-- process. This corresponds to the elaboration judgment @Σ ⊢ c con⇝ Σ'@ which
-- is defined as
--
-- @
--     Σ # c   Γ ⊢ S ▹ S' consig
--    ----------------------------
--    Σ ⊢ alt[c](S) con⇝ Σ, c : S'
-- @
--
-- where @Σ # c@ means that @c@ is not a data constructor in @Σ@.

elabAlt :: String -> String -> ConSig -> Elaborator ()
elabAlt tycon c consig0
  = do let consig = freeToDefinedConSig consig0
       validConSig consig
       when' (typeInSignature c)
           $ throwError ("Constructor already declared: " ++ c)
       consig' <- checkifyConSig consig
       addConstructor c consig'
  where
    validConSig :: ConSig -> Elaborator ()
    validConSig (ConSig _ (Telescope _ retsc)) =
      case body retsc of
        In (Con tc _) ->
          unless (tc == tycon)
            $ throwError $ "The constructor " ++ c ++ " should construct a"
                    ++ " value of the type " ++ tycon ++ " but instead"
                    ++ " produces a " ++ tc
        a ->
          throwError $ "The constructor " ++ c ++ " should constructor a"
                    ++ " value of the type " ++ tycon ++ " but instead"
                    ++ " produces " ++ pretty a





-- | Elaboration of a type constructor is similar to elaborating a data
-- constructor, except it includes elaborations for the constructors as well.
--
-- @
--    Σ # c
--    ⊢ (x0 : A0, ..., xn : An) Type ▹ S' consig
--    Σ, c : S' ⊢ L0 | ... | Ln cons⇝ Σ'
--    --------------------------------------------------------------------
--    Σ ⊢ data c (x0 : A0) ... (xn : An) where L0 | ... | L1 end tycon⇝ Σ'
-- @
--
-- where here @Σ # c@ means that @c@ is not a type constructor in @Σ@.

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon tyconargs alts)
  = do let tyconSig = freeToDefinedConSig (conSigH tyconargs (In Type))
       when' (typeInSignature tycon)
           $ throwError ("Type constructor already declared: " ++ tycon)
       tyconSig' <- checkifyConSig tyconSig
       addConstructor tycon tyconSig'
       mapM_ (uncurry (elabAlt tycon)) alts





-- Elaborating a whole program involves chaining together the elaborations of
-- each kind of declaration. We can define it inductively as follows:
--
-- @
--    -----------------------
--    Σ ; Δ ⊢ e prog⇝ Σ' ; Δ'
--
--      Σ ⊢ data c where L0 | ... | L1 end tycon⇝ Σ'
--    -------------------------------------------------
--    Σ ⊢ (data c where L0 | ... | L1 end ; P) prog⇝ Σ'
--
--       Δ ⊢ let x : A = M end def⇝ Δ'
--    ------------------------------------
--    Δ ⊢ (let x : A = M end ; P) prog⇝ Δ'
-- @

elabProgram :: Program -> Elaborator ()
elabProgram (Program stmts0) = go stmts0
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts