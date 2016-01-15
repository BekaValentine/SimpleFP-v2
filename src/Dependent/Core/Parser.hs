{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Dependent.Core.Parser where

import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad.Reader
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Utils.ABT
import Utils.Vars
import Dependent.Core.ConSig
import Dependent.Core.DeclArg
import Dependent.Core.Term
import Dependent.Core.Program




-- Language Definition

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
              , Token.reservedNames = ["data","case","motive","of","end","where","let","Type"]
              , Token.reservedOpNames = ["|","||","->","\\",":","::","=","."]
              , Token.caseSensitive = True
              }

tokenParser = Token.makeTokenParser languageDef

identifier = Token.identifier tokenParser
reserved = Token.reserved tokenParser
reservedOp = Token.reservedOp tokenParser
parens = Token.parens tokenParser
symbol = Token.symbol tokenParser





-- names

varName = do lookAhead (lower <|> char '_')
             identifier

decName = do lookAhead upper
             identifier


-- term parsers

variable = do x <- varName
              guard (x /= "_")
              return $ Var (Free (FreeVar x))

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- annRight
                return $ annH m t

typeType = do _ <- reserved "Type"
              return $ In Type

binderFunType = do (xs,arg) <- try $ do
                     (xs,arg) <- parens $ do
                       xs <- many1 varName
                       _ <- reservedOp ":"
                       arg <- term
                       return (xs,arg)
                     _ <- reservedOp "->"
                     return (xs,arg)
                   ret <- funRet
                   return $ helperFold (\x -> funH x arg) xs ret

noBinderFunType = do arg <- try $ do
                       arg <- funArg
                       _ <- reservedOp "->"
                       return arg
                     ret <- funRet
                     return $ funH "_" arg ret

funType = binderFunType <|> noBinderFunType

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

assertionPattern = do _ <- reservedOp "."
                      m <- assertionPatternArg
                      return $ ([], assertionPatH m)

varPattern = do x <- varName
                return ([x], Var (Free (FreeVar x)))

noArgConPattern = do c <- decName
                     return $ ([], conPatH c [])

conPattern = do c <- decName
                xsps <- many conPatternArg
                let (xss,ps) = unzip xsps
                return $ (concat xss, conPatH c ps)

parenPattern = parens pattern

conPatternArg = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

assertionPatternArg = parenTerm <|> noArgConData <|> variable <|> typeType

pattern = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

patternSeq = do xsps <- pattern `sepBy` reservedOp "||"
                let (xss,ps) = unzip xsps
                return (concat xss,ps)

consMotivePart = do (xs,a) <- try $ parens $ do
                      xs <- many1 varName
                      _ <- reservedOp ":"
                      a <- term
                      return (xs,a)
                    _ <- reservedOp "||"
                    (xs',as,b) <- caseMotiveParts
                    return (xs ++ xs', replicate (length xs) a ++ as, b)

nilMotivePart = do b <- term
                   return ([], [], b)

caseMotiveParts = consMotivePart <|> nilMotivePart

caseMotive = do (xs,as,b) <- caseMotiveParts
                return $ caseMotiveH xs as b

clause = do (xs,ps) <- try $ do
              xsps <- patternSeq
              _ <- reservedOp "->"
              return xsps
            b <- term
            return $ clauseH xs ps b

caseExp = do _ <- reserved "case"
             ms <- caseArg `sepBy1` reservedOp "||"
             _ <- reservedOp "motive"
             mot <- caseMotive
             _ <- reserved "of"
             _ <- optional (reservedOp "|")
             cs <- clause `sepBy` reservedOp "|"
             _ <- reserved "end"
             return $ caseH ms mot cs

parenTerm = parens term

annLeft = application <|> parenTerm <|> conData <|> variable <|> typeType

annRight = funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

funArg = application <|> parenTerm <|> conData <|> caseExp <|> variable <|> typeType

funRet = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

lamBody = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

appFun = parenTerm <|> variable <|> typeType

appArg = parenTerm <|> noArgConData <|> variable <|> typeType

conArg = parenTerm <|> noArgConData <|> variable <|> typeType

caseArg = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> variable <|> typeType

term = annotation <|> funType <|> application <|> parenTerm <|> lambda <|> conData <|> caseExp <|> variable <|> typeType

parseTerm str = case parse (spaces *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p



-- program parsers

eqTermDecl = do (x,t) <- try $ do
                  _ <- reserved "let"
                  x <- varName
                  _ <- reservedOp ":"
                  t <- term
                  _ <- reservedOp "="
                  return (x,t)
                m <- term
                _ <- reserved "end"
                return $ TermDeclaration x t m

whereTermDecl = do (x,t) <- try $ do
                     _ <- reserved "let"
                     x <- varName
                     _ <- reservedOp ":"
                     t <- term
                     _ <- reserved "where"
                     return (x,t)
                   _ <- optional (reservedOp "|")
                   preclauses <- patternMatchClause x `sepBy1` reservedOp "|"
                   _ <- reserved "end"
                   return $ WhereDeclaration x t preclauses



patternMatchClause x = do _ <- symbol x
                          (xs,ps) <- wherePatternSeq
                          _ <- reservedOp "="
                          b <- term
                          return (xs,ps,b)

wherePattern = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

wherePatternSeq = do xsps <- many wherePattern
                     let (xss,ps) = unzip xsps
                     return (concat xss,ps)

termDecl = eqTermDecl <|> whereTermDecl

alternative = do c <- decName
                 as <- alternativeArgs
                 _ <- reservedOp ":"
                 t <- term
                 return (c,conSigH as t)

alternativeArgs = do argss <- many alternativeArg
                     return (concat argss)

alternativeArg = parens $ do
                   xs <- many1 varName
                   _ <- reservedOp ":"
                   t <- term
                   return $ [ DeclArg x t | x <- xs ]

emptyTypeDecl = do (tycon,tyargs) <- try $ do
                     _ <- reserved "data"
                     tycon <- decName
                     tyargs <- typeArgs
                     _ <- reserved "end"
                     return (tycon,tyargs)
                   return $ TypeDeclaration tycon tyargs []

nonEmptyTypeDecl = do (tycon,tyargs) <- try $ do
                        _ <- reserved "data"
                        tycon <- decName
                        tyargs <- typeArgs
                        _ <- reserved "where"
                        return (tycon,tyargs)
                      _ <- optional (reservedOp "|")
                      alts <- alternative `sepBy` reservedOp "|"
                      _ <- reserved "end"
                      return $ TypeDeclaration tycon tyargs alts

typeArg = parens $ do
            xs <- many1 varName
            _ <- reservedOp ":"
            t <- term
            return $ [ DeclArg x t | x <- xs ]

typeArgs = do argss <- many typeArg
              return (concat argss)

typeDecl = emptyTypeDecl <|> nonEmptyTypeDecl

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl

program = Program <$> many statement



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p