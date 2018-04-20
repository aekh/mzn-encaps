module Translator where

import Tokens
import CST
import qualified Translator.Parser as T
import qualified Translator.Lexer as T

parseTokens :: Tokens -> Either String CST
parseTokens = T.parseTokens

parseString :: String -> Either String CST
parseString str = case lexString str of
  Left err -> Left err
  Right tokens -> case T.parseTokens tokens of
    Left err -> Left err
    Right cst -> Right cst

lexString :: String -> Either String Tokens
lexString = T.lexString
