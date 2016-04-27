module Hopper.Parsing.Term where

import Data.Either (isRight)
import Data.Functor.Identity
import qualified Data.Text as T
import qualified Data.Vector as V
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)

import Hopper.Parsing.Concrete

type Parser = Parsec String ()

pExpr :: Parser Concrete
pExpr = buildExpressionParser table pTerm
    <?> "expression"

pTerm :: Parser Concrete
pTerm = pParens pExpr
    <|> pLam
    <|> pDelay
    <|> pForce
    <|> pLet
    <|> pVar
    <|> pLit
    <?> "simple expression"

pDelay :: Parser Concrete
pDelay = do
  P.reserved lexer "delay"
  expr <- pExpr
  return $ Delay expr

pForce :: Parser Concrete
pForce = do
  P.reserved lexer "force"
  expr <- pExpr
  return $ EnterThunk expr

pLet :: Parser Concrete
pLet = do
  _ <- P.reserved lexer "let"
  name <- P.identifier lexer
  _ <- P.reservedOp lexer "="
  rhs <- pExpr
  _ <- P.reserved lexer "in"
  body <- pExpr
  return $ Let (V.singleton (T.pack name)) rhs body

pLam :: Parser Concrete
pLam = do
  _ <- P.reservedOp lexer "\\"
  args <- many1 (P.identifier lexer)
  let binders = V.fromList $ map T.pack args
  _ <- P.reservedOp lexer "->"
  body <- pExpr
  return $ Lam binders body

pVar :: Parser Concrete
pVar = do
  ident <- P.identifier lexer
  return $ Var $ T.pack ident

lexer :: P.GenTokenParser String u Identity
lexer = P.makeTokenParser $ haskellDef
  { P.reservedNames =
    [ "delay"
    , "force"
    , "let"
    , "in"
    ]
  -- As a compromise, we adopt ocaml-style floating-point operators, to get
  -- around our lack of typechecking.
  , P.reservedOpNames = [":", "=", "->", "\\", "+", "+.", "-", "-.", "*", "*."]
  }

pParens :: ParsecT String u Identity a -> ParsecT String u Identity a
pParens = P.parens lexer

-- eventually: skew min heap for binary space partitioning for picking out
-- "winning" operators to associate first
--
-- eventually (when we have modules): use fully qualified names
table :: OperatorTable String () Identity Concrete
table =
  [ [binary "*" AssocLeft, binary "*." AssocLeft]
  , [binary "+" AssocLeft, binary "-" AssocLeft,
     binary "+." AssocLeft, binary "-." AssocLeft]
  ]

binary :: String -> Assoc -> Operator String () Identity Concrete
binary name = Infix $ do
  let opId = ConcreteOpId (T.pack name)
  P.reservedOp lexer name
  return (\x y -> PrimApp opId (V.fromList [x, y]))

pStrLit, pNumericLit :: Parser Concrete
pStrLit = StrLit . T.pack <$> P.stringLiteral lexer
pNumericLit = NumericLit <$> P.naturalOrFloat lexer

pLit :: Parser Concrete
pLit = pStrLit
   <|> pNumericLit

-- Tests / examples

termParseTest :: String -> IO ()
termParseTest = parseTest pExpr

termParseTest2 :: IO ()
termParseTest2 = do
  let f = print . isRight . parse pExpr "test"
  f "\\x -> y"
  f "\\x y -> y"
  f "let x = delay 1 in force x"
  f "1 + 2 ^ 3"
  f "\"str\""
