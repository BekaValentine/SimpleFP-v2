module Require.Unification.REPL where

import Control.Monad.Reader (runReaderT)
import System.IO
import Debug
import Utils.ABT
import Utils.Env
import Utils.Eval
import Utils.Names
import Utils.Pretty
import Require.Core.ConSig
import Require.Core.Evaluation
import Require.Core.Parser
import Require.Core.Term
import Require.Unification.Elaborator
import Require.Unification.Elaboration
import Require.Unification.TypeChecking



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
    loadProgram :: String
                -> Either String ( Signature
                                 , Definitions
                                 , Context
                                 , Env (String,String) Term
                                 )
    loadProgram src
      = do prog <- parseProgram src
           (_,ElabState sig defs ctx _ _ _ _ _ _ _ _ _ _ _) <-
             runElaborator0 (elabProgram prog)
           let env = definitionsToEnvironment defs
           return (sig,defs,ctx,env)
    
    loadTerm :: Signature
             -> Definitions
             -> Context
             -> Env (String,String) Term
             -> String
             -> Either String Term
    loadTerm sig defs ctx env src
      = do tm0 <- parseTerm src
           let tm = freeToDefined (In . Defined . BareLocal) tm0
               als = [ (Right p,p) | (p,_) <- sig ]
                       ++ [ (Right p,p) | (p,_) <- defs ]
           case runElaborator (infer tm) sig defs ctx als "" [] [] [] of
             Left e  -> Left e
             Right ((etm,_),_) -> runReaderT (paramEval 0 etm) env
    
    evalAndPrint :: Signature
                 -> Definitions
                 -> Context
                 -> Env (String,String) Term
                 -> String
                 -> IO ()
    evalAndPrint _ _ _ _ "" = return ()
    evalAndPrint sig defs ctx env src
      = case loadTerm sig defs ctx env src of
          Left e  -> flushStr ("ERROR: " ++ e ++ "\n")
          Right v -> flushStr (pretty v ++ "\n")

replFile :: String -> IO ()
replFile loc = readFile loc >>= repl