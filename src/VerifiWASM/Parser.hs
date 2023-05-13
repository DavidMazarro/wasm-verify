{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module VerifiWASM.Parser where

import Control.Monad
import Control.Monad.Combinators.Expr
import Data.Either (partitionEithers)
import qualified Data.Text as T
import qualified Data.Text.IO as T (readFile)
import Data.Void
import Path
import Text.Megaparsec
import Text.Megaparsec.Char (alphaNumChar, char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as Lexer
import VerifiWASM.LangTypes

type Parser = Parsec Void T.Text

parseVerifiWASMFile :: Path Abs File -> IO (Maybe Program)
parseVerifiWASMFile filepath = do
  fileContents <- T.readFile $ fromAbsFile filepath
  case runParser programParser (fromAbsFile filepath) fileContents of
    Left e -> putStrLn (errorBundlePretty e) >> return Nothing
    Right program -> return (Just program)

programParser :: Parser Program
programParser = do
  funDefinitions <- many funDefinitionParser
  programFromFunctions funDefinitions <$ eof
  where
    programFromFunctions :: [Either FunctionSpec GhostFunction] -> Program
    programFromFunctions list =
      let (funcs, ghostFuncs) = partitionEithers list
       in Program
            { functions = funcs,
              ghostFunctions = ghostFuncs
            }

funDefinitionParser :: Parser (Either FunctionSpec GhostFunction)
funDefinitionParser =
  Left <$> functionParser
    <|> Right <$> ghostFunctionParser

functionParser :: Parser FunctionSpec
functionParser = do
  keyword "spec"
  name <- identifierParser' True
  args <- parens $ sepByCommas typedIdParser
  spaceConsumer
  keyword "returns"
  returns <- parens $ sepByCommas typedIdParser
  lexeme "{"
  spec <- specParser name
  lexeme "}"
  return $
    FunctionSpec
      { funcName = name,
        funcArgs = args,
        funcReturns = returns,
        specBody = spec
      }

specParser :: Identifier -> Parser SpecBody
specParser name = do
  declarations <- many declarationParser
  let requiresList = [requires | DeclRequires requires <- declarations]
  let ensuresList = [ensures | DeclEnsures ensures <- declarations]

  let lengthRequires = length requiresList
  let lengthEnsures = length ensuresList

  when (lengthRequires > 1) $ failOnLength lengthRequires "requires"
  when (lengthEnsures > 1) $ failOnLength lengthEnsures "ensures"

  -- If no requires is present at parsing, it's considered Requires BTrue
  let requires = if lengthRequires == 0 then Requires BTrue else head requiresList
  -- If no ensures is present at parsing, it's considered Ensures BTrue
  let ensures = if lengthEnsures == 0 then Ensures BTrue else head ensuresList

  let locals = [local | DeclLocals local <- declarations]
  let asserts = [assert | DeclAssert assert <- declarations]

  return
    SpecBody
      { locals = locals,
        requires = requires,
        ensures = ensures,
        asserts = asserts
      }
  where
    failOnLength :: Int -> String -> Parser ()
    failOnLength listLength statementType =
      fail $
        "error in the specification for function "
          <> name
          <> ": there can be at most one requires "
          <> statementType
          <> ", but "
          <> show listLength
          <> " were found."

ghostFunctionParser :: Parser GhostFunction
ghostFunctionParser = do
  keyword "ghostdef"
  name <- identifierParser' True
  args <- parens $ sepByCommas typedIdParser
  spaceConsumer
  keyword "returns"
  returnType <- typeExprParser
  lexeme "{"
  (termination, requires) <- validateTerminationOrRequires name $ many terminationOrRequiresParser
  expr <- exprParser
  lexeme "}"
  return
    GhostFunction
      { ghostName = name,
        ghostArgs = args,
        ghostTermination = termination,
        ghostRequires = requires,
        ghostExpr = expr,
        ghostReturnType = returnType
      }
  where
    validateTerminationOrRequires :: Identifier -> Parser [Either Termination Requires] -> Parser (Termination, Requires)
    validateTerminationOrRequires name list = do
      (terminationList, requiresList) <- partitionEithers <$> list
      let lengthTerminations = length terminationList
      let lengthRequires = length requiresList

      when (lengthTerminations > 1) $ failOnLength name lengthTerminations "decreases"
      when (lengthRequires > 1) $ failOnLength name lengthRequires "requires"

      -- If no decreases is present at parsing, it's considered Decreases []
      let termination = if lengthTerminations == 0 then Decreases [] else head terminationList
      -- If no requires is present at parsing, it's considered Requires BTrue
      let requires = if lengthRequires == 0 then Requires BTrue else head requiresList

      return (termination, requires)

    failOnLength :: Identifier -> Int -> String -> Parser ()
    failOnLength name listLength statementType =
      fail $
        "error in ghostdef "
          <> name
          <> ": there can be at most one "
          <> statementType
          <> " statement, but "
          <> show listLength
          <> " were found."

terminationOrRequiresParser :: Parser (Either Termination Requires)
terminationOrRequiresParser =
  Left <$> terminationParser
    <|> Right <$> requiresParser

terminationParser :: Parser Termination
terminationParser =
  recoverAfterError $
    keyword "decreases"
      >> Decreases
        <$> sepByCommas (lexeme identifierParser)
        <* symbol ";"

declarationParser :: Parser Declaration
declarationParser =
  choice
    [ DeclAssert <$> assertParser,
      DeclEnsures <$> ensuresParser,
      DeclRequires <$> requiresParser,
      DeclLocals <$> localParser
    ]

localParser :: Parser Local
localParser =
  keyword "local"
    >> Local
      <$> sepByCommas typedIdParser
      <* symbol ";"

requiresParser :: Parser Requires
requiresParser =
  recoverAfterError $
    keyword "requires"
      >> Requires <$> exprParser <* symbol ";"

ensuresParser :: Parser Ensures
ensuresParser =
  recoverAfterError $
    keyword "ensures"
      >> (Ensures <$> exprParser) <* symbol ";"

assertParser :: Parser Assert
assertParser = do
  recoverAfterError $ keyword "assert"
  recoverAfterError $ keyword "before"
  lineNumber <- Lexer.decimal
  spaceConsumer
  symbol ":"
  expression <- exprParser
  symbol ";"
  return $ Assert (lineNumber, expression)

operatorTable :: [[Operator Parser Expr]]
operatorTable =
  [ [ prefix "+" id,
      prefix "-" INeg,
      prefixKeyword "not" BNot
    ],
    [ binary "*" IMult,
      binary "/" IDiv,
      binary "%" IMod
    ],
    [ binary "+" IPlus,
      binary "-" IMinus
    ],
    [ binary "<=" BLessOrEq,
      binary "<" BLess,
      binary ">=" BGreaterOrEq,
      binary ">" BGreater
    ],
    [ binary "==" BEq,
      binary "!=" BDistinct
    ],
    [binary "&&" BAnd],
    [binary "^^" BXor],
    [binary "||" BOr],
    [binaryR "=>" BImpl]
  ]

exprParser :: Parser Expr
exprParser = makeExprParser termParser operatorTable

termParser :: Parser Expr
termParser =
  choice
    [ parens exprParser,
      ifThenElseParser,
      absParser,
      BFalse <$ keyword "false",
      BTrue <$ keyword "true",
      try $ IVar <$> lexeme identifierParser,
      IInt <$> lexeme numberParser,
      lexeme funCallParser
    ]

absParser :: Parser Expr
absParser = IAbs <$> between (symbol "|") (symbol "|") exprParser

ifThenElseParser :: Parser Expr
ifThenElseParser = do
  keyword "if"
  ifExpr <- exprParser
  keyword "then"
  thenExpr <- exprParser
  keyword "else"
  IfThenElse ifExpr thenExpr <$> exprParser

funCallParser :: Parser Expr
funCallParser = do
  identifier <- identifierParser' True
  args <- parens $ sepByCommas exprParser
  return $ FunCall identifier args

identifierParser :: Parser Identifier
identifierParser = identifierParser' False

identifierParser' :: Bool -> Parser Identifier
identifierParser' allowParens = do
  underscores <- many $ char '_'
  letters <- some letterChar
  rest <- many (alphaNumChar <|> char '_')
  unless allowParens $ notFollowedBy $ char '('
  let identifier = underscores <> letters <> rest
  checkIsReserved identifier
  where
    checkIsReserved identifier =
      if identifier `elem` reservedKeywords
        then fail $ show identifier <> " cannot be an identifier because it's a reserved keyword."
        else return identifier
    reservedKeywords =
      [ "if",
        "then",
        "else",
        "spec",
        "ghostdef",
        "returns",
        "requires",
        "ensures",
        "assert",
        "decreases",
        "before",
        "not",
        "false",
        "true",
        "i32",
        "i64"
      ]

numberParser :: Parser Integer
numberParser = do
  num <- Lexer.decimal
  notFollowedBy (char '(' <|> char '_' <|> letterChar)
  return num

typeExprParser :: Parser ExprType
typeExprParser = do
  (keyword "bool" >> return ExprBool)
    <|> (keyword "integer" >> return ExprInt)


typedIdParser :: Parser TypedIdentifier
typedIdParser = do
  identifier <- identifierParser
  spaceConsumer
  symbol ":"
  idType <- idTypeParser
  return (identifier, idType)

idTypeParser :: Parser IdType
idTypeParser =
  (keyword "i32" >> return I32)
    <|> (keyword "i64" >> return I64)

----------- Helper functions -----------

spaceConsumer :: Parser ()
spaceConsumer =
  Lexer.space
    space1
    (Lexer.skipLineComment "//")
    (Lexer.skipBlockComment "/*" "*/")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme spaceConsumer

symbol :: T.Text -> Parser T.Text
symbol = Lexer.symbol spaceConsumer

keyword :: T.Text -> Parser T.Text
keyword word = try $ lexeme (string word <* notFollowedBy (alphaNumChar <|> char '('))

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

binary :: T.Text -> (Expr -> Expr -> Expr) -> Operator Parser Expr
binary name f = InfixL (f <$ symbol name)

binaryR :: T.Text -> (Expr -> Expr -> Expr) -> Operator Parser Expr
binaryR name f = InfixR (f <$ symbol name)

binaryKeyword :: T.Text -> (Expr -> Expr -> Expr) -> Operator Parser Expr
binaryKeyword name f = InfixL (f <$ keyword name)

prefix :: T.Text -> (Expr -> Expr) -> Operator Parser Expr
prefix name f = Prefix (f <$ symbol name)

prefixKeyword :: T.Text -> (Expr -> Expr) -> Operator Parser Expr
prefixKeyword name f = Prefix (f <$ keyword name)

sepByCommas :: Parser a -> Parser [a]
sepByCommas parser = parser `sepBy` symbol ","

recoverAfterError :: MonadParsec e s m => m a -> m a
recoverAfterError parser =
  withRecovery
    ( \err -> do
        registerParseError err
        parser
    )
    parser
