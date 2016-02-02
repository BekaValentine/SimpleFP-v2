{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed.

module Dependent.Unification.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Pretty
import Utils.Telescope
import Utils.Vars
import Dependent.Core.ConSig
import Dependent.Core.Program
import Dependent.Core.Term
import Dependent.Unification.Elaborator
import Dependent.Unification.TypeChecking

import Control.Monad
import Control.Monad.Except







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
--    Δ # x   ⊢ A ⇐ Type true   x : A true ⊢ M ⇐ A true
--    -------------------------------------------------
--      Δ ⊢ let x : A = M end def⇝ Δ, x = M : A true
-- @
--
-- where @Δ # x@ means that @x@ is not defined in @Δ@.

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty0 def0) =
  do let ty = freeToDefined (In . Defined) ty0
         def = freeToDefined (In . Defined) def0
     when' (typeInDefinitions n)
         $ throwError ("Term already defined: " ++ n)
     check ty (NormalTerm (In Type))
     ety <- evaluate (SubstitutedTerm ty) -- @ty@ has no metas to substitute.
     extendElab definitions [(n,(def,ty))]
       $ check def ety
     addDeclaration n def ty
elabTermDecl (WhereDeclaration n ty preclauses) =
  case preclauses of
    [] -> throwError "Cannot create an empty let-where definition."
    [(xs,ps,b)] | all isVarPat ps
      -> elabTermDecl
           (TermDeclaration
              n
              ty
              (helperFold lamH xs b))
    (_,ps0,_):_
      -> do let clauses = [ clauseH xs ps b
                          | (xs,ps,b) <- preclauses
                          ]
                xs0 = [ "x" ++ show i | i <- [0..length ps0-1] ]
                lps = length ps0
                mot = motiveAux lps ty
            unless (lps <= functionArgsLength ty)
              $ throwError $ "Cannot build a case expression motive for fewer"
                          ++ " than " ++ show lps ++ " args from the type "
                          ++ pretty ty
            elabTermDecl
              (TermDeclaration
                 n
                 ty
                 (helperFold
                    lamH
                    xs0
                    (caseH (map (Var . Free . FreeVar) xs0) mot clauses)))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False
    
    functionArgsLength :: Term -> Int
    functionArgsLength (In (Fun _ sc)) =
      1 + functionArgsLength (body sc)
    functionArgsLength _ = 0
    
    motiveAux :: Int -> Term -> CaseMotive
    motiveAux i a = caseMotiveH ns as b
      where
        (nsas,b) = motiveAuxAcc [] i a
        (ns,as) = unzip nsas
    
    motiveAuxAcc :: [(String,Term)] -> Int -> Term -> ([(String,Term)], Term)
    motiveAuxAcc acc 0 a =
      (reverse acc, a)
    motiveAuxAcc acc i (In (Fun a sc)) =
      motiveAuxAcc ((x,instantiate0 a):acc) (i-1) b
      where ([x], b) = descope sc
    motiveAuxAcc _ _ _ =
      error $ "This should never be reached because the length arg has"
           ++ " already been guarded against."





-- | Elaboration of a constructor in this variant is a relatively simple
-- process. This corresponds to the elaboration judgment @Σ ⊢ c con⇝ Σ'@ which
-- is defined as
--
-- @
--       Σ # c   Γ ⊢ S consig
--    ---------------------------
--    Σ ⊢ alt[c](S) con⇝ Σ, c : S
-- @
--
-- where @Σ # c@ means that @c@ is not a data constructor in @Σ@.

elabAlt :: String -> String -> ConSig -> Elaborator ()
elabAlt tycon c consig0
  = do let consig = freeToDefinedConSig consig0
       validConSig consig
       when' (typeInSignature c)
           $ throwError ("Constructor already declared: " ++ c)
       checkifyConSig consig
       addConstructor c consig
  where
    validConSig :: ConSig -> Elaborator ()
    validConSig (ConSig (Telescope _ retsc)) =
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





-- | Elaboration of multiple constructors in a type declaration just chains
-- together their effect on the signature:
--
-- @
--    Σ ⊢ L0 con⇝ Σ0   Σ0 ⊢ L1 con⇝ Σ1   ...   Σn-1 ⊢ Ln con⇝ Σn
--    ----------------------------------------------------------
--                  Σ ⊢ L0 | ... | Ln cons⇝ Σn
-- @
--
-- which has the effect of accumulating data constructor signatures.

elabAlts :: String -> [(String, ConSig)] -> Elaborator ()
elabAlts tycon = mapM_ (uncurry (elabAlt tycon))





-- | Elaboration of a type constructor is similar to elaborating a data
-- constructor, except it includes elaborations for the constructors as well.
--
-- @
--    Σ # c
--    ⊢ (x0 : A0, ..., xn : An) Type consig
--   Σ, c : (x0 : A0, ..., xn : An) Type ⊢ L0 | ... | L1 cons⇝ Σ'
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
       checkifyConSig tyconSig
       addConstructor tycon tyconSig
       elabAlts tycon alts





-- Elaborating a whole program involves chaining together the elaborations of
-- each kind of declaration. We can define it inductively as follows:
--
-- @
--    -----------------------
--    Σ ; Δ ⊢ e prog⇝ Σ' ; Δ'
--
--    Σ ⊢ data c where L0 | ... | L1 end tycon⇝ Σ'   Σ' ⊢ P prog⇝ Σ''
--    ---------------------------------------------------------------
--           Σ ⊢ data c where L0 | ... | L1 end ; P prog⇝ Σ''
--
--    Δ ⊢ let x : A = M end def⇝ Δ'   Δ' ⊢ P prog⇝ Δ''
--    ------------------------------------------------
--          Δ ⊢ let x : A = M end ; P prog⇝ Δ''
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