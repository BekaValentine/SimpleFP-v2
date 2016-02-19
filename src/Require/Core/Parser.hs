{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Require.Core.Parser where

import Control.Applicative ((<$>),(<*>),(*>),(<*))
import Control.Monad.Reader
import Data.List (foldl')
import Text.Parsec
import qualified Text.Parsec.Token as Token

import Utils.ABT hiding (shift)
import Utils.Names
import Utils.Plicity
import Utils.Vars
import Require.Core.ConSig
import Require.Core.DeclArg
import Require.Core.Term
import Require.Core.Program




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
              , Token.reservedNames = ["data","case","motive","of","end"
                                      ,"where","let","Type","module","open"
                                      ,"opening","as","using","hiding"
                                      ,"renaming","to","Rec","Quoted"
                                      ,"continue","shift","reset","from","in"
                                      ,"require"
                                      ]
              , Token.reservedOpNames = ["|","||","->","\\",":","::","=",".","`","~"]
              , Token.caseSensitive = True
              }

tokenParser = Token.makeTokenParser languageDef

identifier = Token.identifier tokenParser
reserved = Token.reserved tokenParser
reservedOp = Token.reservedOp tokenParser
parens = Token.parens tokenParser
braces = Token.braces tokenParser
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

dottedName = try $ do
               modName <- decName
               _ <- reservedOp "."
               valName <- varName
               return $ In (Defined (DottedLocal modName valName))

recordProj = do (m,f) <- try $ do
                  m <- recProjArg
                  _ <- reservedOp "."
                  f <- varName
                  return (m,f)
                fieldNames <- many $ do
                  _ <- reservedOp "."
                  varName
                return $ foldl' recordProjH m (f:fieldNames)

recProjArg = recordType <|> recordCon <|> dottedName <|> variable <|> parenTerm <|> typeType

dottedThings = recordProj <|> dottedName

annotation = do m <- try $ do
                  m <- annLeft
                  _ <- reservedOp ":"
                  return m
                t <- annRight
                return $ annH m t

typeType = do _ <- reserved "Type"
              return $ In Type

explFunType = do (xs,arg) <- try $ do
                   (xs,arg) <- parens $ do
                     xs <- many1 varName
                     _ <- reservedOp ":"
                     arg <- term
                     return (xs,arg)
                   _ <- reservedOp "->"
                   return (xs,arg)
                 ret <- funRet
                 return $ helperFold (\x -> funH Expl x arg) xs ret

implFunType = do (xs,arg) <- try $ do
                   (xs,arg) <- braces $ do
                     xs <- many1 varName
                     _ <- reservedOp ":"
                     arg <- term
                     return (xs,arg)
                   _ <- reservedOp "->"
                   return (xs,arg)
                 ret <- funRet
                 return $ helperFold (\x -> funH Impl x arg) xs ret

binderFunType = explFunType <|> implFunType

noBinderFunType = do arg <- try $ do
                       arg <- funArg
                       _ <- reservedOp "->"
                       return arg
                     ret <- funRet
                     return $ funH Expl "_" arg ret

funType = binderFunType <|> noBinderFunType

explArg = do x <- varName
             return (Expl,x)

implArg = do x <- braces varName
             return (Impl,x)

lambdaArg = explArg <|> implArg

lambda = do xs <- try $ do
              _ <- reservedOp "\\"
              many1 lambdaArg
            _ <- reservedOp "->"
            b <- lamBody
            return $ helperFold (\(plic,x) -> lamH plic x) xs b

application = do (f,pa) <- try $ do
                   f <- appFun
                   pa <- appArg
                   return (f,pa)
                 pas <- many appArg
                 return $ foldl' (\f' (plic,a') -> appH plic f' a') f (pa:pas)

bareCon = do conName <- decName
             return $ BareLocal conName

dottedCon = try $ do
              modName <- decName
              _ <- reservedOp "."
              conName <- decName
              return $ DottedLocal modName conName

constructor = dottedCon <|> bareCon

noArgConData = do c <- constructor
                  return $ conH c []

conData = do c <- constructor
             as <- many conArg
             return $ conH c as

assertionPattern = do _ <- reservedOp "."
                      m <- assertionPatternArg
                      return $ ([], assertionPatH m)

varPattern = do x <- varName
                return ([x], Var (Free (FreeVar x)))

noArgConPattern = do c <- constructor
                     return $ ([], conPatH c [])

conPattern = do c <- constructor
                xsps <- many conPatternArg
                let (xss,ps) = unzip xsps
                return $ (concat xss, conPatH c ps)

parenPattern = parens pattern

rawExplConPatternArg = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

explConPatternArg = do (xs,p) <- rawExplConPatternArg
                       return (xs,(Expl,p))

rawImplConPatternArg = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

implConPatternArg = do (xs,p) <- braces $ rawImplConPatternArg
                       return (xs,(Impl,p))

conPatternArg = explConPatternArg <|> implConPatternArg

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

recordType = do _ <- reserved "Rec"
                xts <- braces $ fieldDecl `sepBy` reservedOp ","
                return $ recordTypeH xts
  where
    fieldDecl = do x <- varName
                   _ <- reservedOp ":"
                   t <- term
                   return (x,t)

emptyRecordCon = try $ do
                   braces $ return ()
                   return $ recordConH []

nonEmptyRecordCon = do x <- try $ do
                         _ <- symbol "{"
                         x <- varName
                         _ <- reservedOp "="
                         return x
                       m <- term
                       xms' <- many $ do
                         _ <- reservedOp ","
                         x' <- varName
                         _ <- reservedOp "="
                         m' <- term
                         return (x',m')
                       _ <- symbol "}"
                       return $ recordConH ((x,m):xms')

recordCon = emptyRecordCon <|> nonEmptyRecordCon

bareQuotedType = do _ <- try $ reserved "Quoted"
                    a <- quotedTypeArg
                    return $ quotedTypeH [] a

annotatedQuotedType = do _ <- try $ do
                                reserved "Quoted"
                                symbol "["
                         resets <- many varName
                         _ <- symbol "]"
                         a <- quotedTypeArg
                         return $ quotedTypeH resets a

quotedType = annotatedQuotedType <|> bareQuotedType

quote = do _ <- try $ reservedOp "`"
           m <- quoteArg
           return $ quoteH m

unquote = do _ <- try $ reservedOp "~"
             m <- unquoteArg
             return $ unquoteH m

continue = do _ <- try $ reserved "continue"
              m <- continueArg
              return $ continueH m

shift = do _ <- try $ reserved "shift"
           res <- varName
           _ <- reserved "in"
           m <- shiftArg
           return $ shiftH res m

reset = do _ <- try $ reserved "reset"
           res <- varName
           _ <- reserved "in"
           m <- resetArg
           return $ resetH res m

require = do _ <- try $ reserved "require"
             x <- varName
             _ <- reservedOp ":"
             a <- requireType
             _ <- reserved "in"
             m <- requireBody
             return $ requireH x a m

parenTerm = parens term

annLeft = application <|> continue <|> dottedThings <|> parenTerm <|> conData <|> quotedType <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

annRight = funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

funArg = application <|> continue <|> dottedThings <|> parenTerm <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

funRet = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

lamBody = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

appFun = dottedThings <|> parenTerm <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

rawExplAppArg = dottedThings <|> parenTerm <|> noArgConData <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

explAppArg = do m <- rawExplAppArg
                return (Expl,m)

rawImplAppArg = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

implAppArg = do m <- braces $ rawImplAppArg
                return (Impl,m)

appArg = explAppArg <|> implAppArg

rawExplConArg = dottedThings <|> parenTerm <|> noArgConData <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

explConArg = do m <- rawExplConArg
                return (Expl,m)

rawImplConArg = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

implConArg = do m <- braces $ rawImplConArg
                return (Impl,m)

conArg = explConArg <|> implConArg

caseArg = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

quotedTypeArg = dottedThings <|> parenTerm <|> noArgConData <|> variable <|> typeType <|> quote <|> unquote <|> recordType <|> recordCon

quoteArg = dottedThings <|> parenTerm <|> noArgConData <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

unquoteArg = dottedThings <|> parenTerm <|> noArgConData <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

continueArg = dottedThings <|> parenTerm <|> noArgConData <|> quote <|> unquote <|> variable <|> typeType <|> recordType <|> recordCon

shiftArg = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

resetArg = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

requireType = application <|> continue <|> dottedThings <|> parenTerm <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

requireBody = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

term = annotation <|> funType <|> application <|> continue <|> dottedThings <|> parenTerm <|> lambda <|> shift <|> reset <|> require <|> conData <|> quotedType <|> quote <|> unquote <|> caseExp <|> variable <|> typeType <|> recordType <|> recordCon

parseTerm str = case parse (spaces *> term <* eof) "(unknown)" str of
                  Left e -> Left (show e)
                  Right p -> Right p



-- statement parsers

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
    
letFamilyDecl = do try $ do
                     _ <- reserved "let"
                     _ <- reserved "family"
                     return ()
                   x <- varName
                   args <- typeArgs
                   _ <- reservedOp ":"
                   t <- term
                   _ <- reserved "end"
                   return $ LetFamilyDeclaration x args t

letInstanceDecl = do  try $ do
                        _ <- reserved "let"
                        _ <- reserved "instance"
                        return ()
                      n <- letInstanceName
                      _ <- reserved "where"
                      _ <- optional (reservedOp "|")
                      preclauses <- instancePatternMatchClause n `sepBy1` reservedOp "|"
                      _ <- reserved "end"
                      return $ LetInstanceDeclaration n preclauses

letInstanceBareName = do x <- varName
                         guard (x /= "_")
                         return $ BareLocal x

letInstanceDottedName = try $ do
                       modName <- decName
                       _ <- reservedOp "."
                       valName <- varName
                       return $ DottedLocal modName valName

letInstanceName = letInstanceDottedName <|> letInstanceBareName

instancePatternMatchClause c = do c' <- letInstanceName
                                  guard (c == c')
                                  (xs,ps) <- wherePatternSeq
                                  _ <- reservedOp "="
                                  b <- term
                                  return $ (map fst ps, (xs,map snd ps,b))    

patternMatchClause x = do _ <- symbol x
                          (xs,ps) <- wherePatternSeq
                          _ <- reservedOp "="
                          b <- term
                          return $ (map fst ps, (xs,map snd ps,b))

rawExplWherePattern = assertionPattern <|> parenPattern <|> noArgConPattern <|> varPattern

explWherePattern = do (xs,p) <- rawExplWherePattern
                      return (xs,(Expl,p))

rawImplWherePattern = assertionPattern <|> parenPattern <|> conPattern <|> varPattern

implWherePattern = do (xs,p) <- braces $ rawImplWherePattern
                      return (xs,(Impl,p))

wherePattern = implWherePattern <|> explWherePattern

wherePatternSeq = do xsps <- many wherePattern
                     let (xss,ps) = unzip xsps
                     return (concat xss, ps)

termDecl = letFamilyDecl
       <|> letInstanceDecl
       <|> eqTermDecl
       <|> whereTermDecl

alternative = do c <- decName
                 as <- alternativeArgs
                 _ <- reservedOp ":"
                 t <- term
                 return (c,conSigH as t)

explAlternativeArg = parens $ do
                       xs <- many1 varName
                       _ <- reservedOp ":"
                       t <- term
                       return $ [ DeclArg Expl x t | x <- xs ]

implAlternativeArg = braces $ do
                       xs <- many1 varName
                       _ <- reservedOp ":"
                       t <- term
                       return $ [ DeclArg Impl x t | x <- xs ]

alternativeArg = explAlternativeArg <|> implAlternativeArg

alternativeArgs = do argss <- many alternativeArg
                     return (concat argss)

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

explTypeArg = parens $ do
                xs <- many1 varName
                _ <- reservedOp ":"
                t <- term
                return $ [ DeclArg Expl x t | x <- xs ]

implTypeArg = braces $ do
                xs <- many1 varName
                _ <- reservedOp ":"
                t <- term
                return $ [ DeclArg Impl x t | x <- xs ]

typeArg = explTypeArg <|> implTypeArg

typeArgs = do argss <- many typeArg
              return (concat argss)

dataFamilyDecl = do try $ do
                      _ <- reserved "data"
                      _ <- reserved "family"
                      return ()
                    tycon <- decName
                    tyargs <- typeArgs
                    _ <- reserved "end"
                    return $ DataFamilyDeclaration tycon tyargs

dataInstanceDecl = do try $ do
                        _ <- reserved "data"
                        _ <- reserved "instance"
                        return ()
                      tycon <- constructor
                      _ <- reserved "where"
                      _ <- optional (reservedOp "|")
                      alts <- alternative `sepBy` reservedOp "|"
                      _ <- reserved "end"
                      return $ DataInstanceDeclaration tycon alts

typeDecl = emptyTypeDecl
       <|> nonEmptyTypeDecl
       <|> dataFamilyDecl
       <|> dataInstanceDecl

resetDecl = do _ <- try $ reserved "reset"
               res <- varName
               _ <- reserved "from"
               a <- term
               _ <- reserved "to"
               b <- term
               _ <- reserved "end"
               return $ ResetDeclaration res a b

statement = TmDecl <$> termDecl
        <|> TyDecl <$> typeDecl
        <|> ResetDecl <$> resetDecl





-- open settings

oAs = optionMaybe $ do
        _ <- reserved "as"
        decName

oHidingUsing = optionMaybe (hiding <|> using)
  where
    hiding = do _ <- reserved "hiding"
                ns <- parens (sepBy (varName <|> decName) (reservedOp ","))
                return (Hiding ns)
    using = do _ <- reserved "using"
               ns <- parens (sepBy (varName <|> decName) (reservedOp ","))
               return (Using ns)

oRenaming = do m <- openRenamingP
               case m of
                 Nothing -> return []
                 Just ns -> return ns
  where
    openRenamingP = optionMaybe $ do
                      _ <- reserved "renaming"
                      parens (sepBy (varRen <|> decRen) (reservedOp ","))
    varRen = do n <- varName
                _ <- reserved "to"
                n' <- varName
                return (n,n')
    decRen = do n <- decName
                _ <- reserved "to"
                n' <- decName
                return (n,n')

openSettings = OpenSettings <$> decName
                            <*> oAs
                            <*> oHidingUsing
                            <*> oRenaming




-- modules

modulOpen = do n <- try $ do
                 _ <- reserved "module"
                 n <- decName
                 _ <- reserved "opening"
                 return n
               _ <- optional (reserved "|")
               settings <- sepBy openSettings (reserved "|")
               _ <- reserved "where"
               stmts <- many statement
               _ <- reserved "end"
               return $ Module n settings stmts

modulNoOpen = do n <- try $ do
                   _ <- reserved "module"
                   n <- decName
                   _ <- reserved "where"
                   return n
                 stmts <- many statement
                 _ <- reserved "end"
                 return $ Module n [] stmts

modul = modulOpen <|> modulNoOpen





-- programs

program = Program <$> many modul



parseProgram :: String -> Either String Program
parseProgram str
  = case parse (spaces *> program <* eof) "(unknown)" str of
      Left e -> Left (show e)
      Right p -> Right p