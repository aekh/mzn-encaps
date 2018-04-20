module Translator.Lexer where

import Text.Parsec
import Control.Monad (void)

import Tokens

type Lexer = Parsec String ()

lexString :: String -> Either String Tokens
lexString fstr = case parse lexer "lexer" fstr of
  Left err -> Left $ "Lexical error. No match: " ++ show err
  Right val -> Right val

lexer :: Lexer Tokens
lexer = soc >> many (oneToken <* soc) <* eof

oneToken :: Lexer Token
oneToken = (char ';' >> return TStmtEnd)
           <|> try (string ">=" >> return TGeq)
           <|> try (string "==" >> return TEqEq)
           <|> (char '=' >> return TEq)
           <|> try (string "::" >> return TColonColon)
           <|> (char ':' >> return TColon)
           <|> (char '(' >> return TLParen)
           <|> (char ')' >> return TRParen)
           <|> (char ',' >> return TComma)
           <|> (string ".." >> return TEllipsis)
           <|> try (string "[|" >> return TLBracketBar)
           <|> (char '[' >> return TLBracket)
           <|> (char ']' >> return TRBracket)
           <|> (char '{' >> return TLBrace)
           <|> (char '}' >> return TRBrace)
           <|> (string "\\/" >> return TOr)
           <|> (string "/\\" >> return TAnd)
           <|> try (string "<->" >> return TEquivalence)
           <|> try (string "<-" >> return TLImplies)
           <|> try (string "<=" >> return TLeq)
           <|> (char '<' >> return TLt)
           <|> (char '>' >> return TGt)
           <|> (string "!=" >> return TNeq)
           <|> try (string "++" >> return TPlusPlus)
           <|> (char '+' >> return TPlus)
           <|> try (string "->" >> return TRImplies)
           <|> (char '-' >> return TMinus)
           <|> (char '*' >> return TStar)
           <|> (char '/' >> return TSlash)
           <|> try (string "|]" >> return TBarRBracket)
           <|> (char '|' >> return TBar)
           <|> try (TFloatNumber <$> float)
           <|> TIntNumber <$> natural
           <|> tString
           <|> identifierOrKeyword
  where tString = do
          char '"'
          s <- manyTill anyChar (char '"')
          return $ TString s
        identifierOrKeyword = do
          first <- letter
          rest <- many (letter <|> digit <|> char '_')
          return $ case first:rest of
            "array" -> TArray
            "bool" -> TBool
            "constraint" -> TConstraint
            "diff" -> TDiff
            "div" -> TDiv
            "else" -> TElse
            "elseif" -> TElseIf
            "endif" -> TEndIf
            "false" -> TFalse
            "float" -> TFloat
            "function" -> TFunction
            "if" -> TIf
            "in" -> TIn
            "include" -> TInclude
            "int" -> TInt
            "intersect" -> TIntersect
            "let" -> TLet
            "maximize" -> TMaximize
            "minimize" -> TMinimize
            "mod" -> TMod
            "not" -> TNot
            "output" -> TOutput
            "of" -> TOf
            "par" -> TPar
            "predicate" -> TPredicate
            "satisfy" -> TSatisfy
            "set" -> TSet
            "solve" -> TSolve
            "subset" -> TSubset
            "superset" -> TSuperset
            "symdiff" -> TSymDiff
            "then" -> TThen
            "true" -> TTrue
            "union" -> TUnion
            "var" -> TVar
            "where" -> TWhere
            "xor" -> TXor
            identifier -> TIdentifier identifier

natural :: Lexer Int
natural = try octal
          <|> try hexadecimal
          <|> decimal
  where octal = do
          string "0x"
          digits <- many1 $ oneOf "01234567"
          return (read digits :: Int)
        hexadecimal = do
          string "0o"
          digits <- many1 $ oneOf "0123456789ABCDEFabcdef"
          return (read digits :: Int)
        decimal = do
          digits <- many1 digit
          return (read digits :: Int)

float :: Lexer Float
float = try (expOn frac)
        <|> try frac
        <|> expOn natural
  where frac = do
          integral <- natural
          char '.'
          fractional <- natural
          return (read (show integral ++ "." ++ show fractional) :: Float)
        expOn baseParser = do
          base <- baseParser
          oneOf "Ee"
          sign <- char '-' <|> option '+' (char '+')
          exponent <- natural
          return (read (show base ++ 'e' : sign : show exponent) :: Float)

soc :: Lexer ()
soc = skipMany (void space <|> void comment <|> void (try multiComment))

comment :: Lexer String
comment = char '%' >> many (noneOf "\n\r")

multiComment :: Lexer String
multiComment = string "/*"
               >> manyTill anyChar (try (string "*/"))
