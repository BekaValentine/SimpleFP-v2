module DependentImplicit.Unification.REPL where

import Control.Monad.Reader (runReaderT)
import System.IO

import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Pretty
import DependentImplicit.Core.ConSig
import DependentImplicit.Core.Evaluation
import DependentImplicit.Core.Parser
import DependentImplicit.Core.Term
import DependentImplicit.Unification.Elaborator
import DependentImplicit.Unification.Elaboration
import DependentImplicit.Unification.TypeChecking



flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ p prompt action = do 
   result <- prompt
   if p result 
      then return ()
      else action result >> until_ p prompt action

repl :: String -> IO ()
repl src = case loadProgram src of
             Left e -> flushStr ("ERROR: " ++ e ++ "\n")
             Right (sig,defs,ctx,env)
               -> do hSetBuffering stdin LineBuffering
                     until_ (== ":quit")
                            (readPrompt "$> ")
                            (evalAndPrint sig defs ctx env)
  where
    loadProgram :: String -> Either String (Signature,Definitions,Context,Env String Term)
    loadProgram src
      = do prog <- parseProgram src
           (_,ElabState sig defs ctx _ _) <- runElaborator0 (elabProgram prog)
           let env = definitionsToEnvironment defs
           return (sig,defs,ctx,env)
    
    loadTerm :: Signature -> Definitions -> Context -> Env String Term -> String -> Either String Term
    loadTerm sig defs ctx env src
      = do tm0 <- parseTerm src
           let tm = freeToDefined (In . Defined) tm0
           case runElaborator (infer tm) sig defs ctx of
             Left e  -> Left e
             Right ((etm,_),_) -> runReaderT (eval etm) env
    
    evalAndPrint :: Signature -> Definitions -> Context -> Env String Term -> String -> IO ()
    evalAndPrint _ _ _ _ "" = return ()
    evalAndPrint sig defs ctx env src
      = case loadTerm sig defs ctx env src of
          Left e  -> flushStr ("ERROR: " ++ e ++ "\n")
          Right v -> flushStr (pretty v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl