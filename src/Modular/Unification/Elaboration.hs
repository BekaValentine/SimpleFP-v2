{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed.

module Modular.Unification.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Names
import Utils.Plicity
import Utils.Pretty
import Utils.Telescope
import Utils.Vars
import Modular.Core.ConSig
import Modular.Core.Program
import Modular.Core.Term
import Modular.Unification.Elaborator
import Modular.Unification.TypeChecking

import Control.Monad
import Control.Monad.Except
import Data.List (inits,nub,(\\),groupBy,sort,intersect,partition)







-- | We can add a new defined value declaration given a name, term, and type.

addDeclaration :: (String,String) -> Term -> Term -> Elaborator ()
addDeclaration n def ty = addElab definitions [(n,(def,ty))]


-- | We can add a new constructor by giving a name and a signature.

addConstructor :: (String,String) -> ConSig -> Elaborator ()
addConstructor c consig = addElab signature [(c,consig)]


-- | We can add an alias to the current collection of aliases.

addAlias :: String -> Elaborator ()
addAlias n =
  do als <- getElab aliases
     m <- getElab moduleName
     putElab aliases ((Left n,(m,n)):als)


-- | We can add a module name to the current collection.

addModuleName :: String -> Elaborator ()
addModuleName m
  = do ms <- getElab moduleNames
       unless (not (m `elem` ms))
         $ throwError $ "A module is already declared with the name " ++ m
       putElab moduleNames (m:ms)





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
--          Δ ⊢ let x : A = M end def⇝ Δ, MOD.x = M' : A' true
-- @
--
-- where @Δ # x@ means that @x@ is not defined in @Δ@.

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty0 def0) =
  do let ty = freeToDefined (In . Defined . BareLocal) ty0
         def = freeToDefined (In . Defined . BareLocal) def0
     m <- getElab moduleName
     when' (typeInDefinitions (Absolute m n))
         $ throwError ("Term already defined: " ++ n)
     addAlias n
     elty <- check ty (NormalTerm (In Type))
     ety <- evaluate (SubstitutedTerm elty) -- @ty@ has no metas to substitute.
     eldef <- extendElab definitions [((m,n),(def,normTerm ety))]
                $ check def ety
     addDeclaration (m,n) eldef (normTerm ety)
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
      in CaseMotive (BindingTelescope ascs bsc)
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
--       Σ # c   Γ ⊢ S ▹ S' consig
--    --------------------------------
--    Σ ⊢ alt[c](S) con⇝ Σ, MOD.c : S'
-- @
--
-- where @Σ # c@ means that @c@ is not a data constructor in @Σ@.

elabAlt :: String -> String -> ConSig -> Elaborator ()
elabAlt tycon c consig0
  = do let consig = freeToDefinedConSig consig0
       validConSig consig
       m <- getElab moduleName
       when' (typeInSignature (Absolute m c))
           $ throwError ("Constructor already declared: " ++ c)
       addAlias c
       consig' <- checkifyConSig consig
       addConstructor (m,c) consig'
  where
    validConSig :: ConSig -> Elaborator ()
    validConSig (ConSig _ (BindingTelescope _ retsc)) =
      case body retsc of
        In (Con tc _) ->
          unless (tc == BareLocal tycon)
            $ throwError $ "The constructor " ++ c ++ " should construct a"
                    ++ " value of the type " ++ tycon ++ " but instead"
                    ++ " produces a " ++ showName tc
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
--    Σ, MOD.c : S' ⊢ L0 | ... | Ln cons⇝ Σ'
--    --------------------------------------------------------------------
--    Σ ⊢ data c (x0 : A0) ... (xn : An) where L0 | ... | L1 end tycon⇝ Σ'
-- @
--
-- where here @Σ # c@ means that @c@ is not a type constructor in @Σ@.

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon tyconargs alts)
  = do let tyconSig = freeToDefinedConSig (conSigH tyconargs (In Type))
       m <- getElab moduleName
       when' (typeInSignature (Absolute m tycon))
           $ throwError ("Type constructor already declared: " ++ tycon)
       addAlias tycon
       tyconSig' <- checkifyConSig tyconSig
       addConstructor (m,tycon) tyconSig'
       mapM_ (uncurry (elabAlt tycon)) alts





-- | We can require that a module exists to be imported.

ensureModuleExists :: String -> Elaborator ()
ensureModuleExists m
  = do ms <- getElab moduleNames
       unless (m `elem` ms)
         $ throwError $ "The module " ++ m ++ " is not a known module."


-- | We can ensure that the open-as settings are valid by checking that there
-- isn't already an open module with that name.

openAsIsValid :: Maybe String -> Elaborator ()
openAsIsValid Nothing = return ()
openAsIsValid (Just m')
  = do ms <- getElab moduleNames
       unless (not (m' `elem` ms))
         $ throwError $ "The module name " ++ m' ++ " is already in use."


-- | We can ensure that the hiding-using settings are valid  by checking that
-- all of the relevant names exist in the module in question.

hidingUsingIsValid :: String -> Maybe HidingUsing -> Elaborator ()
hidingUsingIsValid _ Nothing = return ()
hidingUsingIsValid m (Just hu')
  = do defs <- getElab definitions
       sig <- getElab signature
       let ns = nub $ case hu' of
                  Hiding ns' -> ns'
                  Using ns' -> ns'
           known = nub $ [ n | ((_,n),(_,_)) <- defs ]
                      ++ [ n | ((_,n),_) <- sig ]
           missing = ns \\ known
       unless (null missing)
         $ throwError $ "The module " ++ m
                     ++ " does not declare these symbols: "
                     ++ unwords missing


-- | We can ensure that the renaming settings are valid by checking that all
-- of the renamed symbols actually exist, and that the new names don't
-- conflict with other names that have been opened.

renamingIsValid :: String
                -> Maybe String
                -> Maybe HidingUsing
                -> [(String,String)]
                -> Elaborator ()
renamingIsValid m a hu r
  = do defs <- getElab definitions
       sig <- getElab signature
       let ns = nub [ n | (n,_) <- r ]
           known = nub $ [ n | ((m',n),(_,_)) <- defs, m' == m ]
                      ++ [ n | ((m',n),_) <- sig, m' == m ]
           missing = ns \\ known
       unless (null missing)
         $ throwError $ "The module " ++ m
                     ++ " does not declare these symbols: "
                     ++ unwords ns
       let knownBeingUsed = case hu of
                              Nothing -> known
                              Just (Using used) -> used
                              Just (Hiding hidden) -> known \\ hidden
           missingUsed = ns \\ knownBeingUsed
       unless (null missingUsed)
         $ throwError $ "The following symbols are not being opened: "
                        ++ unwords missingUsed
       let ns' = [ n' | (_,n') <- r ]
           preserved = known \\ ns
           overlappingNames =
             [ x | x:xs <- groupBy (==) (sort (ns' ++ preserved))
                 , length xs /= 0
                 ]
       unless (null overlappingNames)
         $ throwError $ "These symbols will be overlapping when the module "
                     ++ m ++ " is opened: " ++ unwords overlappingNames
       als <- getElab aliases
       let combine = case a of
                       Nothing -> Left
                       Just m' -> \n' -> Right (m',n')
           mns' = nub [ combine n' | (_,n') <- r ]
           knownAls = nub [ al | (al,_) <- als ]
           overlap = intersect mns' knownAls
           showLR (Left n0) = n0
           showLR (Right (m0,n0)) = m0 ++ "." ++ n0
       unless (null overlap)
         $ throwError $ "These symbols are already in scope: "
                     ++ unwords (map showLR overlap)


-- | We can ensure that open settings are valid by ensuring the module to open
-- exists, that the open-as setting is valid, that the hiding-using settings
-- are valid, and finally that the renaming settings are valid.

ensureOpenSettingsAreValid :: [OpenSettings] -> Elaborator ()
ensureOpenSettingsAreValid oss
  = forM_ oss $ \(OpenSettings m a hu r) -> do
      ensureModuleExists m
      openAsIsValid a
      hidingUsingIsValid m hu
      renamingIsValid m a hu r


-- | We can compute new aliases from open settings.

newAliases :: Signature -> Definitions -> [OpenSettings] -> Aliases
newAliases _ _ [] = []
newAliases sig defs (os:oss)
  = let als  = newAliasesFromSettings os
        als' = newAliases sig defs oss
    in als' ++ als
  where    
    newAliasesFromSettings :: OpenSettings -> Aliases
    newAliasesFromSettings (OpenSettings m a hu r)
      = let openedSymbols = [ (m',c) | ((m',c),_) <- sig, m' == m ]
                         ++ [ (m',x) | ((m',x),(_,_)) <- defs, m' == m ]
            usedSymbols = used hu openedSymbols
            renamedSymbols = renamed r usedSymbols
            asedSymbols = ased a renamedSymbols
        in asedSymbols
    
    used :: Maybe HidingUsing -> [(String,String)] -> [(String,String)]
    used Nothing            = id
    used (Just (Hiding ns)) = filter (\(_,n) -> not (n `elem` ns))
    used (Just (Using ns))  = filter (\(_,n) -> (n `elem` ns))
    
    renamed :: [(String,String)]
            -> [(String,String)]
            -> [(String,(String,String))]
    renamed r mns = [ (maybe n id (lookup n r), (m,n)) | (m,n) <- mns ]
    
    ased :: Maybe String
         -> [(String,(String,String))]
         -> [(Either String (String,String), (String,String))]
    ased Nothing   ns = [ (Left x, (m,n)) | (x,(m,n)) <- ns ]
    ased (Just m') ns = [ (Right (m',x), (m,n)) | (x,(m,n)) <- ns ]


-- | We can extend the current aliases with some open settings.

extendAliases :: [OpenSettings] -> Elaborator a -> Elaborator a
extendAliases settings tc
  = do ensureOpenSettingsAreValid settings
       als <- getElab aliases
       sig <- getElab signature
       defs <- getElab definitions
       let newAls = newAliases sig defs settings ++ als
       putElab aliases newAls
       x <- tc
       putElab aliases als
       return x





-- Elaborating a module involves chaining together the elaborations of each
-- kind of declaration. We can define it inductively as follows:
--
-- @
--    -----------------------
--    Σ ; Δ ⊢ e mod⇝ Σ' ; Δ'
--
--    Σ ⊢ data c where L0 | ... | L1 end tycon⇝ Σ'   Σ' ⊢ P mod⇝ Σ''
--    ---------------------------------------------------------------
--           Σ ⊢ data c where L0 | ... | L1 end ; P mod⇝ Σ''
--
--    Δ ⊢ let x : A = M end def⇝ Δ'   Δ' ⊢ P mod⇝ Δ''
--    ------------------------------------------------
--          Δ ⊢ let x : A = M end ; P mod⇝ Δ''
-- @

elabModule :: Module -> Elaborator ()
elabModule (Module m settings stmts0)
  = do addModuleName m
       putElab moduleName m
       ensureOpenSettingsAreValid settings
       als <- getElab aliases
       sig <- getElab signature
       defs <- getElab definitions
       let newAls = newAliases sig defs settings ++ als
       putElab aliases newAls
       go stmts0
       putElab aliases als
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts





-- | We can sort modules by dependencies. This sort separates modules into
-- groups where each group has dependencies only on modules in previous
-- groups. We do this by splitting a set of remaining modules into two groups,
-- those that have dependencies only in previous modules, and those that
-- don't, and then we split on the ones that don't, over and over in this way,
-- until we've finished, or until the remaining modules have none that have
-- dependencies only in previous modules, which indicates circular
-- dependencies.

sortModules :: [Module] -> Elaborator [Module]
sortModules mods0 = go [] mods0
  where
    splitModules :: [String] -> [Module] -> Elaborator ([Module], [Module])
    splitModules prev mods
      = let (next,rest) =
              partition (\(Module _ settings _) ->
                all (\s -> openModule s `elem` prev) settings) mods
        in if null next
           then throwError $ "The following modules have circular dependencies which prevent resolution: "
                          ++ unwords [ n | Module n _ _ <- rest ]
           else return (next,rest)
    
    go :: [String] -> [Module] -> Elaborator [Module]
    go _ []
      = return []
    go prev mods
      = do (next,rest) <- splitModules prev mods
           let newPrev = [ n | Module n _ _ <- next ]
           rest' <- go (newPrev ++ prev) rest
           return (next ++ rest')





-- | We can elaborate a whole program by sorting the modules it defines, and
-- then by elaborating them in that order. 

elabProgram :: Program -> Elaborator ()
elabProgram (Program mods)
  = do sortedMods <- sortModules mods
       mapM_ elabModule sortedMods