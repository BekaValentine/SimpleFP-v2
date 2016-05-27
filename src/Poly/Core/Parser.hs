{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}





-- | This module defines how to parser a program in the simply typed lambda
-- calculus w/ non-parametric user defined types (eg Bool, Nat).

module Poly.Core.Parser where

import Utils.ABT
import Utils.Vars
import Poly.Core.ConSig
import Poly.Core.Term
import Poly.Core.Type
import Poly.Core.Program

import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad (guard)
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token





languageDef :: Token.LanguageDef st
languageDef = Token.LanguageDef
                { Token.commentStart = "{-"
                , Token.commentEnd = "-}"
                , Token.commentLine = "--"
                , Token.nestedComments = True
                , Token.identStart = letter <|> char '_'
                , Token.identLetter = alphaNum <|> char '_' <|> char '\''
                , Token.opStart = oneOf ""
                , Token.opLetter = oneOf ""
                , Token.reservedNames = ["data","case","of","end","where","let"]
                , Token.reservedOpNames = ["|","->","\\",":","=","||"]
                , Token.caseSensitive = True
                }

tokenParser = Token.makeTokenParser languageDef

identifier = Token.identifier tokenParser
reserved = Token.reserved tokenParser
reservedOp = Token.reservedOp tokenParser
parens = Token.parens tokenParser
symbol = Token.symbol tokenParser
whiteSpace = Token.whiteSpace tokenParser





-- Parsers for identifiers

varName = do lookAhead (lower <|> char '_')
             identifier

decName = do lookAhead upper
             identifier





-- Type parsers

noArgTypeCon = do c <- decName
                  return $ tyConH c []

typeCon = tyConH <$> decName <*> many tyConArg

funType = do arg <- try $ do
               arg <- funLeft
               _ <- reservedOp "->"
               return arg
             ret <- funRight
             return $ funH arg ret

typeVar = do x <- varName
             guard (x /= "_")
             return $ Var (Free (FreeVar x))

forallType = do _ <- reserved "forall"
                xs <- many1 varName
                _ <- reservedOp "."
                b <- forallBody
                return $ helperFold forallH xs b

parenType = parens datatype

tyConArg = parenType <|> noArgTypeCon <|> typeVar

funLeft = parenType <|> typeCon <|> typeVar

funRight = funType <|> parenType <|> forallType <|> typeCon <|> typeVar

forallBody = funType <|> parenType <|> forallType <|> typeCon <|> typeVar

datatype = funType <|> parenType <|> forallType <|> typeCon <|> typeVar





-- Term parsers

variable = do x <- varName
              guard (x /= "_")
              return $ Var (Free (FreeVar x))

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- datatype
                return $ annH m t

lambda = do _ <- reservedOp "\\"
            xs <- many1 varName
            _ <- reservedOp "->"
            b <- lamBody
            return $ helperFold lamH xs b

application = do (f,a) <- try $ do
                   f <- appFun
                   a <- appArg
                   return (f,a)
                 as <- many appArg
                 return $ foldl' appH f (a:as)

noArgConData = do c <- decName
                  return $ conH c []

conData = do c <- decName
             as <- many conArg
             return $ conH c as

varPattern = do x <- varName
                return (Var (Free (FreeVar x)),[x])

noArgConPattern = do c <- decName
                     return $ (conPatH c [], [])

conPattern = do c <- decName
                psxs <- many conPatternArg
                let (ps,xs) = unzip psxs
                return $ (conPatH c ps, concat xs)

parenPattern = parens pattern

conPatternArg = parenPattern <|> noArgConPattern <|> varPattern

pattern = parenPattern <|> conPattern <|> varPattern

clause = do psxs <- try $ do
              psxs <- pattern `sepBy` reservedOp "||"
              _ <- reservedOp "->"
              return psxs
            b <- term
            let ps = map fst psxs
                xs = concat (map snd psxs)
            return $ clauseH xs ps b

caseExp = do _ <- reserved "case"
             m <- caseArg `sepBy` reservedOp "||"
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ caseH m cs

parenTerm = parens term

annLeft = application <|> parenTerm <|> conData <|> variable

lamBody = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable

appFun = parenTerm <|> variable

appArg = parenTerm <|> noArgConData <|> variable

conArg = parenTerm <|> noArgConData <|> variable

caseArg = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> variable

term = annotation <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable

parseTerm str = case parse (whiteSpace *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p





-- Program parsers

eqTermDecl = do (x,t) <- try $ do
                  _ <- reserved "let"
                  x <- varName
                  _ <- reservedOp ":"
                  t <- datatype
                  _ <- reservedOp "="
                  return (x,t)
                m <- term
                _ <- reserved "end"
                return $ TermDeclaration x t m

whereTermDecl = do (x,t) <- try $ do
                     _ <- reserved "let"
                     x <- varName
                     _ <- reservedOp ":"
                     t <- datatype
                     _ <- reserved "where"
                     return (x,t)
                   _ <- optional (reservedOp "|")
                   preclauses <- patternMatchClause x `sepBy1` reservedOp "|"
                   _ <- reserved "end"
                   return $ WhereDeclaration x t preclauses

patternMatchClause x = do _ <- symbol x
                          psxs <- many patternMatchPattern
                          _ <- reservedOp "="
                          b <- term
                          let ps = map fst psxs
                              xs = concat (map snd psxs)
                          return (ps,xs,b)

patternMatchPattern = parenPattern <|> noArgConPattern <|> varPattern

termDecl = eqTermDecl <|> whereTermDecl

alternative = do c <- decName
                 as <- many alternativeArg
                 return (c,as)

alternativeArg = parenType <|> typeCon <|> typeVar

typeDecl = do _ <- reserved "data"
              tycon <- decName
              params <- many varName
              alts <- option [] $ do
                _ <- reservedOp "="
                alternative `sepBy` reservedOp "|"
              _ <- reserved "end"
              return $ TypeDeclaration
                         tycon
                         params
                         [ (c, conSigH params as (tyConH tycon (map (Var . Free . FreeVar) params))) | (c,as) <- alts ]

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement





-- | A convenience function that will parse or return the parse error string.

parseProgram :: String -> Either String Program
parseProgram str =
  case parse (whiteSpace *> program <* eof) "(unknown)" str of
    Left e -> Left (show e)
    Right p -> Right p