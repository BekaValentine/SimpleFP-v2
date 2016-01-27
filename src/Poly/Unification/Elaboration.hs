{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed.

module Poly.Unification.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Vars
import Poly.Core.ConSig
import Poly.Core.Term
import Poly.Core.Type
import Poly.Core.Program
import Poly.Unification.Elaborator
import Poly.Unification.TypeChecking

import Control.Monad.Except








-- | We can add a new defined value declaration given a name, term, and type.

addDeclaration :: String -> Term -> Type -> Elaborator ()
addDeclaration n def ty = addElab definitions [(n,(def,ty))]


-- | We can add a new type constructor by giving a name and a type constructor
-- signature.

addTypeConstructor :: String -> TyConSig -> Elaborator ()
addTypeConstructor n sig = addElab (signature.typeConstructors) [(n,sig)]


-- | We can add a new data constructor by given a type constructor name, a
-- name for the data constructor, and a list of arg types from which to build
-- a constructor signature.

addConstructor :: String -> ConSig -> Elaborator ()
addConstructor n consig = addElab (signature.dataConstructors) [(n,consig)]





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
--      Δ # x   A type   x : A true ⊢ M ⇐ A true
--    --------------------------------------------
--    Δ ⊢ let x : A = M end def⇝ Δ, x = M : A true
-- @
--
-- where @Δ # x@ means that @x@ is not defined in @Δ@.

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty def0) =
  do let def = freeToDefined (In . Defined) def0
     when' (typeInDefinitions n)
         $ throwError ("Term already defined: " ++ n)
     isType ty
     extendElab definitions [(n,(def,ty))]
       $ check def ty
     addDeclaration n def ty
elabTermDecl (WhereDeclaration n ty preclauses) =
  case preclauses of
    [] -> throwError "Cannot create an empty let-where definition."
    [(ps,xs,b)] | all isVarPat ps
      -> elabTermDecl
           (TermDeclaration
              n
              ty
              (helperFold lamH xs b))
    (ps0,_,_):_
      -> let clauses = [ clauseH xs ps b
                       | (ps,xs,b) <- preclauses
                       ]
             xs0 = [ "x" ++ show i | i <- [0..length ps0-1] ]
         in elabTermDecl
              (TermDeclaration
                 n
                 ty
                 (helperFold
                    lamH
                    xs0
                    (caseH (map (Var . Free . FreeVar) xs0) clauses)))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False





-- | Elaboration of a constructor in this variant is a relatively simple
-- process. This corresponds to the elaboration judgment @Σ ⊢ c con S ⇝ Σ'@
-- which is defined as
--
-- @
--         Σ # c   S consig
--    ---------------------------
--    Σ ⊢ alt[c](S) con⇝ Σ, c : S
-- @
--
-- where @Σ # c@ means that @c@ is not a data constructor in @Σ@.

elabAlt :: String -> ConSig -> Elaborator ()
elabAlt n consig =
  do when' (typeInSignature n)
         $ throwError ("Constructor already declared: " ++ n)
     checkifyConSig consig
     addConstructor n consig





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

elabAlts :: [(String, ConSig)] -> Elaborator ()
elabAlts = mapM_ (uncurry elabAlt)





-- | Elaboration of a type constructor is similar to elaborating a data
-- constructor, except it includes elaborations for the constructors as well.
--
-- @
--    Σ # c   Ai type   Σ, c tycon n ⊢ L0 | ... | Ln cons⇝ Σ'
--    -------------------------------------------------------
--    Σ ⊢ data c A0 ... An where L0 | ... | L1 end tycon⇝ Σ'
-- @
--
-- where here @Σ # c@ means that @c@ is not a type constructor in @Σ@.

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts) =
  do when' (tyconExists tycon)
         $ throwError ("Type constructor already declared: " ++ tycon)
     addTypeConstructor tycon (TyConSig (length params))
     elabAlts alts





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