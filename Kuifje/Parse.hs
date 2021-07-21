{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Kuifje.Parse where

import Kuifje.Syntax
import Prelude
import System.IO 
import Data.Ratio
import Data.Set
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import Text.Parsec (ParsecT)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Functor.Identity

--
-- Parsec Language Setup
--

languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "if"
                                      , "then"
                                      , "else"
                                      , "fi"
                                      , "while"
                                      , "do"
                                      , "od"
                                      , "set"
                                      , "skip"
                                      , "true"
                                      , "false"
                                      , "~"
                                      , "&&"
                                      , "||"
                                      , "hid"
                                      , "vis"
                                      , "print"
                                      , "leak"
                                      , "observe"
                                      , "uniform"
                                      , "|"
                                      ]

            , Token.reservedOpNames = ["+"
                                      , "-"
                                      , "^"
                                      , "*"
                                      , "/"
                                      , "div"
                                      , "<"
                                      , ">"
                                      , "~"
                                      , ":="
                                      , "<="
                                      , ">="
                                      , "=="
                                      , "!="
                                      , "&&"
                                      , "||"
                                      , "%"
                                      , "@"
                                      ]
            }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
brackets   = Token.brackets   lexer -- exterior choice
angles     = Token.angles     lexer -- interior choice
braces     = Token.braces     lexer 
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace
natural    = Token.natural    lexer
integer    = Token.integer    lexer
symbol     = Token.symbol     lexer

--
-- Generic
--

s << t = do { x <- s;  t; return x }

decimalRat :: Parser Rational
decimalRat = 
  do ns <- many1 digit
     ms <- try (char '.' >> many digit) <|> return [] 
     let pow10 = toInteger $ length ms
     let (Right n) = parse natural "" (ns ++ ms)
     return (n % (10 ^ pow10))

kChoice :: (a -> a -> Expr -> a) -> Parser (a -> a -> a)
kChoice c =
      do symbol "["
         expr <- expression
         symbol "]"
         return $ \x y -> c x y expr  

--
-- Statements
--

statements :: Parser Stmt
statements =
  do whiteSpace
     list <- sepEndBy statement (semi >> whiteSpace)
     return $ case list of
               [] -> Skip     -- the empty program is skip
               [s] -> s       -- a single statement is just itself
               ps -> Seq ps   -- multiple statements are sequenced

statement :: Parser Stmt
statement = buildExpressionParser sOperators sTerm

sOperators =
   [[Infix (kChoice Echoice) AssocLeft]]

sTerm :: Parser Stmt
sTerm = (braces statements
         <|> assignStmt
         <|> ifStmt
         <|> whileStmt
         <|> skipStmt
         <|> vidStmt
         <|> leakStmt) << whiteSpace

ifStmt :: Parser Stmt
ifStmt =
  do reserved "if"
     cond  <- expression
     reserved "then"
     stmt1 <- statements
     reserved "else"
     stmt2 <- statements
     reserved "fi"
     return $ If cond stmt1 stmt2

whileStmt :: Parser Stmt
whileStmt =
  do reserved "while"
     cond <- expression
     reserved "do"
     stmt <- statements
     reserved "od"
     return $ While cond stmt

assignStmt :: Parser Stmt
assignStmt =
  do var  <- identifier
     reservedOp ":="
     expr <- expression 
     return $ Assign var expr

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

vidStmt :: Parser Stmt
vidStmt = 
  do reserved "vis" 
     var <- identifier
     return $ Vis var

leakStmt :: Parser Stmt
leakStmt = 
  do reserved "leak" <|> reserved "print" <|> reserved "observe"
     expr <- expression
     return $ Leak expr

--
-- Expressions
--

expression :: Parser Expr
expression =
   buildExpressionParser eOperators eTerm << whiteSpace
      <?> "expression"

eOperators = 
        [ [Prefix (reservedOp "-"   >> return Neg               )          ]
        , [Prefix (reservedOp "~"   >> return Not               )          ]
        , [Infix  (reservedOp "*"   >> return (ABinary Multiply)) AssocLeft,
           Infix  (reservedOp "/"   >> return (ABinary Divide  )) AssocLeft,
           Infix  (reservedOp "div" >> return (ABinary IDivide )) AssocLeft,
           Infix  (reservedOp "+"   >> return (ABinary Add     )) AssocLeft,
           Infix  (reservedOp "%"   >> return (ABinary Rem     )) AssocLeft,
           Infix  (reservedOp "^"   >> return (ABinary Pow     )) AssocLeft,
           Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
        , [Infix  (reservedOp "&&"  >> return (BBinary And     )) AssocLeft,
           Infix  (reservedOp "||"  >> return (BBinary Or      )) AssocLeft]
        , [Infix  (kChoice Ichoice)                               AssocLeft]
        , [Infix  (reservedOp ">"   >> return (RBinary Gt)      ) AssocLeft] 
        , [Infix  (reservedOp "<"   >> return (RBinary Lt)      ) AssocLeft] 
        , [Infix  (reservedOp ">="  >> return (RBinary Ge)      ) AssocLeft] 
        , [Infix  (reservedOp "<="  >> return (RBinary Le)      ) AssocLeft] 
        , [Infix  (reservedOp "=="  >> return (RBinary Eq)      ) AssocLeft] 
        , [Infix  (reservedOp "!="  >> return (RBinary Ne)      ) AssocLeft]
        , [Infix  (reservedOp "@"   >> return Tuple             ) AssocLeft] 
        ]

eTerm :: Parser Expr
eTerm = (parens expression
        <|> (reserved "true"  >> return (BoolConst True ) <?> "true")
        <|> (reserved "false" >> return (BoolConst False) <?> "false")
        <|> ifExpr
        <|> setExpr
        <|> try uniformFromSet
        <|> try uniformIchoices
        <|> try uniformSetVar
        <|> try uniformIchoicesListComp
        <|> notUniformIchoices
        <|> (liftM RationalConst (try decimalRat) <?> "rat")
        <|> (liftM Var identifier <?> "var")
        <?> "eTerm") << whiteSpace

ifExpr =
  do reserved "if"
     cond <- expression
     reserved "then"
     expr1 <- expression
     reserved "else"
     expr2 <- expression
     reserved "fi"
     return $ ExprIf cond expr1 expr2
   <?> "if-expr"

uniformIchoices = 
        do reserved "uniform"
           reservedOp "["
           list <- sepBy expression (symbol ",")
           reservedOp "]"
           return $ Ichoices list

notUniformIchoices = 
        do reservedOp "["
           list <- sepBy expression (symbol ",")
           reservedOp "]"
           return $ INUchoices list

uniformIchoicesListComp = 
        do reserved "uniform"
           reservedOp "["
           l <- integer
           symbol ".."
           r <- integer
           reservedOp "]"
           return $ Ichoices [(RationalConst (x % 1)) | x <- [l..r]]

uniformFromSet = 
        do reserved "uniform"
           reserved "set"
           reservedOp "{"
           list <- sepBy expression (symbol ",")
           reservedOp "}"
           let values = fromList list
           return $ SetIchoice (Eset values)

uniformSetVar = 
        do reserved "uniform"
           expr <- liftM Var identifier
           return $ SetIchoice expr

setExpr = 
        do reserved "set"
           reservedOp "{"
           list <- sepBy expression (symbol ",")
           reservedOp "}"
           let values = fromList list
           return $ Eset values

-- Output only
parseString :: String -> Stmt
parseString str =
        case parse statements "" str of
          Left e  -> error $ show e
          Right r -> r

parseFile :: String -> IO Stmt
parseFile file =
        do program  <- readFile file
           case parse statements "" program of
                Left e  -> print e >> fail "parse error"
                Right r -> return r
