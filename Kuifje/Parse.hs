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
import qualified Text.Parsec.Indent as Indent
import qualified Text.Parsec as ParsecCl
import qualified Text.Parsec.Indent.Explicit as Explicit
import qualified Text.Parsec.Indent.Internal as Internal
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
                                      , "geometric"
                                      , "|"
                                      , "switch"
                                      , "case"
                                      , "default"
                                      , "break"
                                      , "function"
                                      , "fun"
                                      , "nuf"
                                      , "call"
                                      , "returns"
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
                                      , "::"
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
         <|> funcStmt
         <|> returnStmt
         <|> try callStmt
         <|> try samplingStmt
         <|> try supportStmt
         <|> assignStmt
         <|> ifStmt
         <|> whileStmt
         <|> skipStmt
         <|> vidStmt
         <|> leakStmt) << whiteSpace

elseStmt :: Parser (Expr,Stmt)
elseStmt = 
   do ref <- indentationBlock
      reserved "else"
      reservedOp ":"
      body <- codeBlock ref
      -- For else statements, the condition should be always true
      input <- getInput
--      error ("Input is:\n" ++ (show input))
      return $ ((RBinary Eq (RationalConst (1 % 1)) (RationalConst (1 % 1))) , body)

ifCondStmt :: Parser (Expr,Stmt)
ifCondStmt =
   do ref <- indentationBlock
      reserved "if"
      cond <- expression
      reservedOp ":"
      body <- codeBlock ref
      input <- getInput
      return $ (cond, body)

elifCondStmt :: Parser (Expr,Stmt)
elifCondStmt =
   do ref <- indentationBlock
      reserved "elif"
      cond <- expression
      reservedOp ":"
      body <- codeBlock ref
      input <- getInput
      return $ (cond, body)
      
checkIndent :: Expr -> Internal.Indentation -> Internal.Indentation -> Bool
checkIndent expr ref pos = 
   if expr == (RBinary Eq (RationalConst (1 % 1)) (RationalConst (1 % 1)))
      then False
      else (isInBlock ref pos) 

-- | Parses a block of lines at the same indentation level starting at the
-- current position
getIfBlock :: Bool -> Internal.Indentation -> Parser Stmt
getIfBlock False _ = return $ Skip
getIfBlock True ref = do
      pos <- indentation
      (cond, stmt) <- option ((RBinary Eq (RationalConst (1 % 1)) (RationalConst (1 % 1))),Skip) (elifCondStmt <|> elseStmt)
      elseBlock <- (getIfBlock (checkIndent cond ref pos) ref)
      return $ (If cond stmt elseBlock)

ifStmt :: Parser Stmt
ifStmt =
   do ref <- indentation
      (cond, stmt) <- ifCondStmt
      pos <- indentation
      elseBlock <- (getIfBlock (isInBlock ref pos) ref)
      input <- getInput
      setInput (";" ++ input)
      return $ (If cond stmt elseBlock)

-- | Obtain the current indentation, to be used as a reference later.
indentation :: Monad m => ParsecT s u m Internal.Indentation
indentation = do
    pos <- getPosition
    return $! Internal.Indentation {Internal.iLine = sourceLine pos, Internal.iColumn = sourceColumn pos}

-- | Obtain the current indentation, to be used as a reference later.
indentationBlock :: Monad m => ParsecT s u m Internal.Indentation
indentationBlock = do
    pos <- getPosition
    return $! Internal.Indentation {Internal.iLine = sourceLine pos, Internal.iColumn = ((sourceColumn pos) +  1)}


-- | Verifies if the position is in the same block as the reference position
isInBlock :: Internal.Indentation -> Internal.Indentation -> Bool
isInBlock ref pos = (Internal.iColumn pos >= Internal.iColumn ref)

-- | Parses a block of lines at the same indentation level starting at the
-- current position
getBlock :: Bool -> Internal.Indentation -> Parser Stmt
getBlock False _ = return $ (Seq [])
getBlock True ref = do 
      stmt <- getNextStmt
      pos <- indentation
      (Seq ls) <- option (Seq []) (getBlock (isInBlock ref pos) ref)
      return $ (Seq (stmt : ls))

-- | Collect the block of instruction in the same indentation level
codeBlock :: Internal.Indentation -> Parser Stmt
codeBlock ref = do
    stmt <- (getBlock (isInBlock ref ref) ref)
    return $ stmt

-- | Returns the next Statement in the program
getNextStmt :: Parser Stmt
getNextStmt =
  do whiteSpace
     stmt <- statement
     semi
     return $ stmt

funcStmt :: Parser Stmt
funcStmt = 
  do ref <- indentationBlock
     reserved "def"
     name <- identifier
     whiteSpace
     -- Input Parameters
     inputs <- sepBy (parens identifier) (symbol ",")
     whiteSpace
     reserved ":"
     body <- codeBlock ref
     -- Output Parameters - Only in the end of the function:
     input <- getInput
     setInput (";" ++ input)
--     error ("Body Func is:\n" ++ (show input) ++ "\n\n")
     return $ FuncStmt name body inputs

returnStmt :: Parser Stmt
returnStmt =
  do reserved "return"
     outputs <- sepBy expression (symbol ",")
     return $ ReturnStmt outputs
     
callStmt :: Parser Stmt
callStmt =
  do output <- identifier
     reserved "="
     name <- identifier
     reservedOp "("
     inputs <- sepBy expression (symbol ",")
     reservedOp ")"
     return $ CallStmt name inputs [output]

whileStmt :: Parser Stmt
whileStmt =
  do ref <- indentationBlock
     reserved "while"
     cond <- expression
     reservedOp ":"
     stmt <- codeBlock ref
     input <- getInput
     setInput (";" ++ input)
     return $ While cond stmt 

assignStmt :: Parser Stmt
assignStmt =
  do var  <- identifier
     reservedOp "="
     expr <- expression
     return $ Assign var expr

samplingStmt :: Parser Stmt
samplingStmt =
  do var <- identifier
     reservedOp "<-"
     expr <- expression
     return $ Sampling var expr

supportStmt :: Parser Stmt
supportStmt =
  do var <- identifier
     reservedOp "="
     reserved "set"
     expr <- expression
     return $ Support var expr

skipStmt :: Parser Stmt
skipStmt = reserved "skip" >> return Skip

vidStmt :: Parser Stmt
vidStmt = 
  do reserved "vis" 
     var <- identifier
     return $ Vis var

leakStmt :: Parser Stmt
leakStmt = 
  do reserved "leak" <|> reserved "observe" -- <|> reserved "print"
     reservedOp "("
     expr <- expression
     reservedOp ")"
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
           Infix  (reservedOp "&"   >> return (ABinary Intersection)) AssocLeft,
           Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
        , [Infix  (reservedOp "in"  >> return (SBinary In        )) AssocLeft,
           Infix  (reservedOp "nin"  >> return (SBinary NIn      )) AssocLeft,
           Infix  (reservedOp "isSub"  >> return (SBinary IsSubOf)) AssocLeft]
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
        <|> try notUniformIchoices
        <|> geometricIchoices
        <|> (liftM RationalConst (try decimalRat) <?> "rat")
        <|> (liftM Var identifier <?> "var")
        <?> "eTerm") << whiteSpace

elseExpr :: Parser (Expr,Expr)
elseExpr =
   do reserved "else"
      reservedOp ":"
      body <- expression
      -- For else statements, the condition should be always true
      return $ ((RBinary Eq (RationalConst (1 % 1)) (RationalConst (1 % 1))) , body)

ifCondExpr :: Parser (Expr,Expr)
ifCondExpr =
   do reserved "if"
      cond <- expression
      reservedOp ":"
      body <- expression
      input <- getInput
      return $ (cond, body)

elifCondExpr :: Parser (Expr,Expr)
elifCondExpr =
   do reserved "elif"
      cond <- expression
      reservedOp ":"
      body <- expression
      input <- getInput
      return $ (cond, body)

-- | Parses a block of lines at the same indentation level starting at the
-- current position
getIfBlockExpr :: Parser Expr
getIfBlockExpr = do
      -- Option provides a default value, that is an indetermination.
      -- If the values at this point add up to one, it will be naturally skiped.
      -- Otherwise the default value will generate an error, as the Expression does not add up to one.
      (cond, exprIf) <- option ((RBinary Ne (RationalConst (1 % 1)) (RationalConst (1 % 1))), (RationalConst (1 % 1))) (elifCondExpr <|> elseExpr) 
      if cond == (RBinary Eq (RationalConst (1 % 1)) (RationalConst (1 % 1)))
      then return $ exprIf
      else if cond == (RBinary Ne (RationalConst (1 % 1)) (RationalConst (1 % 1)))
           then error ("\nIf expression not in the format.\nPossible else statement missing.\n")
           else do
              exprElse <- getIfBlockExpr
              return $ ExprIf cond exprIf exprElse

ifExpr =
  do (cond, exprIf) <- ifCondExpr
     exprElse <- getIfBlockExpr
     return $ ExprIf cond exprIf exprElse

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

getParam :: Integer -> [Expr] -> Expr
getParam 0 ls = (head ls)
getParam n ls = getParam (n-1) (tail ls)

geometricIchoices =
  do reserved "geometric"
     reservedOp "("
     params <- sepBy expression (symbol ",")
     reservedOp ")"
     return $ Geometric (getParam 0 params) (getParam 1 params) (getParam 2 params) (getParam 3 params)

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
