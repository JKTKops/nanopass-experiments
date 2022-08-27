module Passes.LispIL.Parse
  ( parser ) where

import Text.Parsec

import Language.LispIL.Parsed

-- super simple parser, this is just for playing around.
parser :: String -> Either ParseError LispIL
parser = runParser parseLispIL () "parser"

type Parser = Parsec String ()

parseLispIL :: Parser LispIL
parseLispIL = sexp <|> var

sexp :: Parser LispIL
sexp = do
  _ <- char '('
  es <- parseLispIL `sepBy` spaces
  _ <- char ')'
  return $ SExp es

var :: Parser LispIL
var = Var <$> many1 alphaNum
