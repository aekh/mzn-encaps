module Translator.Parser where

import Text.Parsec hiding (tokens)

import CST
import Tokens

type Parser = Parsec Tokens ()

satisfy' :: (Token -> Bool) -> Parser Token
satisfy' f = tokenPrim show
             (\src _ _ -> incSourceColumn src 1)
             (\x -> if f x then Just x else Nothing)

parseTokens :: Tokens -> Either String Model
parseTokens tokens = case parse parser "parser" tokens of
    Left err -> Left $ "Parser error. No match: " ++ show err
    Right m -> Right m

parser :: Parser Model
parser = model

----------------------------------------------------------------------
-- ITEMS
----------------------------------------------------------------------

model :: Parser Model
model = Model <$> many item <* eof

item :: Parser Item
item = (IIncludeItem <$> stmt includeItem)
       <|> (IVarDeclItem <$> stmt varDeclItem)
       <|> (IAssignItem <$> stmt assignItem)
       <|> (IConstraintItem <$> stmt constraintItem)
       <|> (ISolveItem <$> stmt solveItem)
       <|> (IOutputItem <$> stmt outputItem)
       <|> (IPredicateItem <$> stmt predicateItem)
       <|> (IFunctionItem <$> stmt functionItem)
  where stmt itemParser =
          itemParser <* tStmtEnd

tiExprAndId :: Parser TiExprAndId
tiExprAndId = do
  te <- tiExpr
  tColon
  i <- ident
  return $ TiExprAndId te i

includeItem :: Parser IncludeItem
includeItem = tInclude >> IncludeItem <$> stringLiteral

varDeclItem :: Parser VarDeclItem
varDeclItem = do
  teai <- tiExprAndId
  anns <- annotations
  e <- try (tEq >> Just <$> expr) <|> return Nothing
  return $ VarDeclItem teai anns e

assignItem :: Parser AssignItem
assignItem = do
  i <- ident
  tEq
  e <- expr
  return $ AssignItem i e

constraintItem :: Parser ConstraintItem
constraintItem = tConstraint >> (ConstraintItem <$> expr)

solveItem :: Parser SolveItem
solveItem = try smax <|> try smin <|> ssat
  where smax = do
          tSolve
          anns <- annotations
          tMaximize
          e <- expr
          return $ SMaximize anns e
        smin = do
          tSolve
          anns <- annotations
          tMinimize
          e <- expr
          return $ SMinimize anns e
        ssat = do
          tSolve
          anns <- annotations
          tSatisfy
          return $ SSatisfy anns

outputItem :: Parser OutputItem
outputItem = tOutput >> (OutputItem <$> expr)

predicateItem :: Parser PredicateItem
predicateItem = PredicateItem <$> (tPredicate >> operationItemTail)

functionItem :: Parser FunctionItem
functionItem = do
  tFunction
  te <- tiExpr
  tColon
  oit <- operationItemTail
  return $ FunctionItem te oit

operationItemTail :: Parser OperationItemTail
operationItemTail = do
  i <- ident
  p <- params
  a <- annotations
  e <- try (tEq >> Just <$> expr) <|> return Nothing
  return $ OperationItemTail i p a e

params :: Parser Params
params = Params <$> inTParen (tComma `separated` tiExprAndId)

----------------------------------------------------------------------
-- TYPE-INST EXPRESSIONS
----------------------------------------------------------------------

tiExpr :: Parser TiExpr
tiExpr = TiExpr <$> baseTiExpr

baseTiExpr :: Parser BaseTiExpr
baseTiExpr = do
  vp <- varPar
  btet <- baseTiExprTail
  return $ BaseTiExpr vp btet

varPar :: Parser VarPar
varPar = (tVar >> return Var)
         <|> (tPar >> return Par)
         <|> return Par

baseTiExprTail :: Parser BaseTiExprTail
baseTiExprTail = (BIdent <$> ident)
                 <|> (tBool >> return BBool)
                 <|> try range
                 <|> (tInt >> return BInt)
                 <|> (tFloat >> return BFloat)
                 <|> (BSetTiExprTail <$> setTiExprTail)
                 <|> (BArrayTiExprTail <$> arrayTiExprTail)
                 <|> BSet <$> inTBrace (tComma `separated` expr)
  where range = do
          ne1 <- numExpr
          tEllipsis
          ne2 <- numExpr
          return $ BRange ne1 ne2

setTiExprTail :: Parser SetTiExprTail
setTiExprTail = do
  tSet >> tOf
  sint <|> sset <|> srange
  where sint = tInt >> return SInt
        sset =
          SSet <$> inTBrace (tComma `separated` expr)
        srange = do
          ne1 <- numExpr
          tEllipsis
          ne2 <- numExpr
          return $ SRange ne1 ne2

arrayTiExprTail :: Parser ArrayTiExprTail
arrayTiExprTail = do
  tArray
  iss <- inTBracket $ tComma `separated1` tiExpr
  tOf
  te <- tiExpr
  return $ ArrayTiExprTail iss te

----------------------------------------------------------------------
-- EXPRESSIONS
----------------------------------------------------------------------

expr :: Parser Expr
expr = Expr <$> expr12

expr12 :: Parser Expr12
expr12 = let rest :: Parser Expr12 -> Parser Expr12
             rest x = do
               e <- x
               (tEquivalence >> rest (EEquivalence e <$> expr11))
                 <|> return e
         in rest (EExpr11 <$> expr11)

expr11 :: Parser Expr11
expr11 = let rest :: Parser Expr11 -> Parser Expr11
             rest x = do
               e <- x
               (tRImplies >> rest (ERImplies e <$> expr10))
                 <|> (tLImplies >> rest (ELImplies e <$> expr10))
                 <|> return e
         in rest (EExpr10 <$> expr10)

expr10 :: Parser Expr10
expr10 = let rest :: Parser Expr10 -> Parser Expr10
             rest x = do
               e <- x
               (tOr >> rest (EOr e <$> expr9))
                 <|> (tXor >> rest (EXor e <$> expr9))
                 <|> return e
         in rest (EExpr9 <$> expr9)

expr9 :: Parser Expr9
expr9 = let rest :: Parser Expr9 -> Parser Expr9
            rest x = do
              e <- x
              (tAnd >> rest (EAnd e <$> expr8))
                <|> return e
        in rest (EExpr8 <$> expr8)

expr8 :: Parser Expr8
expr8 = do
  e <- expr7
  (tLt >> ELt e <$> expr7)
    <|> (tGt >> EGt e <$> expr7)
    <|> (tLeq >> ELeq e <$> expr7)
    <|> (tGeq >> EGeq e <$> expr7)
    <|> (tEqEq >> EEqEq e <$> expr7)
    <|> (tEq >> EEq e <$> expr7)
    <|> (tNeq >> ENeq e <$> expr7)
    <|> return (EExpr7 e)

expr7 :: Parser Expr7
expr7 = do
 e <- expr6
 (tIn >> EIn e <$> expr6)
   <|> (tSubset >> ESubset e <$> expr6)
   <|> (tSuperset >> ESuperset e <$> expr6)
   <|> return (EExpr6 e)

expr6 :: Parser Expr6
expr6 = let rest :: Parser Expr6 -> Parser Expr6
            rest x = do
              e <- x
              (tUnion >> rest (EUnion e <$> expr5))
                <|> (tDiff >> rest (EDiff e <$> expr5))
                <|> (tSymDiff >> rest (ESymDiff e <$> expr5))
                <|> return e
        in rest (EExpr5 <$> expr5)

expr5 :: Parser Expr5
expr5 = do
  e <- expr4
  (tEllipsis >> EEllipsis e <$> expr4)
    <|> return (EExpr4 e)

expr4 :: Parser Expr4
expr4 = let rest :: Parser Expr4 -> Parser Expr4
            rest x = do
              e <- x
              (tPlus >> rest (EPlus e <$> expr3))
                <|> (tMinus >> rest (EMinus e <$> expr3))
                <|> return e
        in rest (EExpr3 <$> expr3)

expr3 :: Parser Expr3
expr3 = let rest :: Parser Expr3 -> Parser Expr3
            rest x = do
              e <- x
              (tStar >> rest (EStar e <$> expr2))
                <|> (tDiv >> rest (EDiv e <$> expr2))
                <|> (tMod >> rest (EMod e <$> expr2))
                <|> (tSlash >> rest (ESlash e <$> expr2))
                <|> (tIntersect >> rest (EIntersect e <$> expr2))
                <|> return e
        in rest (EExpr2 <$> expr2)

expr2 :: Parser Expr2
expr2 = do
  e <- expr1
  (tPlusPlus >> EPlusPlus e <$> expr2)
    <|> return (EExpr1 e)

expr1 :: Parser Expr1
expr1 = EExprAtom <$> exprAtom

exprAtom :: Parser ExprAtom
exprAtom = do
  eah <- exprAtomHead
  eat <- exprAtomTail
  anns <- annotations
  return $ ExprAtom eah eat anns

exprAtomHead :: Parser ExprAtomHead
exprAtomHead = try buoea
               <|> EExpr <$> inTParen expr
               <|> EIfThenElseExpr <$> ifThenElseExpr
               <|> EBoolLiteral <$> boolLiteral
               <|> EIntLiteral <$> intLiteral
               <|> EFloatLiteral <$> floatLiteral
               <|> EStringLiteral <$> stringLiteral
               <|> try (EArrayComp <$> arrayComp)
               <|> EArrayLiteral <$> arrayLiteral
               <|> EArrayLiteral2d <$> arrayLiteral2d
               <|> ELetExpr <$> letExpr
               <|> try (EGenCallExpr <$> genCallExpr)
               <|> try (ECallExpr <$> callExpr)
               <|> EIdentOrQuotedOp <$> identOrQuotedOp
               <|> try (ESetComp <$> setComp)
               <|> ESetLiteral <$> setLiteral
 where buoea = do
          buo <- builtinUnOp
          ea <- exprAtom
          return $ EBuiltinUnOp buo ea

exprAtomTail :: Parser ExprAtomTail
exprAtomTail = try aateat
               <|> return EATNothing

  where aateat = do
          aat <- arrayAccessTail
          eat <- exprAtomTail
          return $ ExprAtomTail aat eat

-- Incomplete
numExpr :: Parser NumExpr
numExpr = NumExpr <$> numExpr4

numExpr4 :: Parser NumExpr4
numExpr4 = let rest :: Parser NumExpr4 -> Parser NumExpr4
               rest x = do
                 e <- x
                 (tPlus >> rest (NPlus e <$> numExpr3))
                   <|> (tMinus >> rest (NMinus e <$> numExpr3))
                   <|> return e
           in rest (NNumExpr3 <$> numExpr3)

numExpr3 :: Parser NumExpr3
numExpr3 = let rest :: Parser NumExpr3 -> Parser NumExpr3
               rest x = do
                 e <- x
                 (tStar >> rest (NStar e <$> numExpr1))
                   <|> (tDiv >> rest (NDiv e <$> numExpr1))
                   <|> (tMod >> rest (NMod e <$> numExpr1))
                   <|> (tSlash >> rest (NSlash e <$> numExpr1))
                   <|> return e
           in rest (NNumExpr1 <$> numExpr1)

-- Incomplete
numExpr1 :: Parser NumExpr1
numExpr1 = NNumExprAtom <$> numExprAtom

numExprAtom :: Parser NumExprAtom
numExprAtom = do
  neah <- numExprAtomHead
  eat <- exprAtomTail
  anns <- annotations
  return $ NumExprAtom neah eat anns

numExprAtomHead :: Parser NumExprAtomHead
numExprAtomHead = try bnuonea
                  <|> NNumExpr <$> inTParen numExpr
                  <|> NIfThenElseExpr <$> ifThenElseExpr
                  <|> NIntLiteral <$> intLiteral
                  <|> NFloatLiteral <$> floatLiteral
                  <|> NLetExpr <$> letExpr
                  <|> try (NGenCallExpr <$> genCallExpr)
                  <|> try (NCallExpr <$> callExpr)
                  <|> NIdentOrQuotedOp <$> identOrQuotedOp
  where bnuonea = do
          bnuo <- builtinNumUnOp
          nea <- numExprAtom
          return $ NBuiltinNumUnOp bnuo nea

builtinUnOp :: Parser BuiltinUnOp
builtinUnOp = (tNot >> return BNot)
              <|> BBuiltinNumUnOp <$> builtinNumUnOp

builtinNumUnOp :: Parser BuiltinNumUnOp
builtinNumUnOp = (tPlus >> return BPositive)
                 <|> (tMinus >> return BNegative)

boolLiteral :: Parser BoolLiteral
boolLiteral = (tTrue >> return (BoolLiteral True))
              <|> (tFalse >> return (BoolLiteral False))

intLiteral :: Parser IntLiteral
intLiteral = IntLiteral <$> tIntNumber

floatLiteral :: Parser FloatLiteral
floatLiteral = FloatLiteral <$> tFloatNumber

stringLiteral :: Parser StringLiteral
stringLiteral = StringLiteral <$> tString

setLiteral :: Parser SetLiteral
setLiteral = slset
  where slset = do
          tLBrace
          es <- tComma `separated` expr
          tRBrace
          return $ SetLiteral es

setComp :: Parser SetComp
setComp = do
  tLBrace
  e <- expr
  tBar
  ct <- compTail
  tRBrace
  return $ SetComp e ct

compTail :: Parser CompTail
compTail = do
  gs <- tComma `separated1` generator
  e <- try (tWhere >> (Just <$> expr))
       <|> return Nothing
  return $ CompTail gs e

generator :: Parser Generator
generator = do
  is <- tComma `separated1` ident
  tIn
  e <- expr
  return $ Generator is e

arrayLiteral :: Parser ArrayLiteral
arrayLiteral =
  ArrayLiteral <$> inTBracket (tComma `separated` expr)

arrayComp :: Parser ArrayComp
arrayComp = do
  tLBracket
  e <- expr
  tBar
  ct <- compTail
  tRBracket
  return $ ArrayComp e ct

arrayLiteral2d :: Parser ArrayLiteral2d
arrayLiteral2d = do
  tLBracketBar
  ess <- tBar `separated` (tComma `separated` expr)
  tBarRBracket
  return $ ArrayLiteral2d ess

arrayAccessTail :: Parser ArrayAccessTail
arrayAccessTail = do
  tLBracket
  es <- tComma `separated1` expr
  tRBracket
  return $ ArrayAccessTail es

ifThenElseExpr :: Parser IfThenElseExpr
ifThenElseExpr = do
  tIf
  c <- expr
  tThen
  e <- expr
  ces <- many elseIfs
  tElse
  ee <- expr
  tEndIf
  return $ IfThenElseExpr c e ces ee
  where elseIfs = do
          tElseIf
          c <- expr
          tThen
          e <- expr
          return (c, e)

-- TODO weird that call with no args have no parens in doc
callExpr :: Parser CallExpr
callExpr = do
  ioqo <- identOrQuotedOp
  ps <- inTParen (tComma `separated` expr)
  return $ CallExpr ioqo ps

letExpr :: Parser LetExpr
letExpr = do
  tLet
  tLBrace
  lis <- tStmtEnd `separated1` letItem
  try tStmtEnd <|> return TStmtEnd
  tRBrace
  tIn
  e <- expr
  return $ LetExpr lis e

letItem :: Parser LetItem
letItem = LVarDeclItem <$> varDeclItem
          <|> LConstraintItem <$> constraintItem

genCallExpr :: Parser GenCallExpr
genCallExpr = do
  ioqo <- identOrQuotedOp
  tLParen
  ct <- compTail
  tRParen
  tLParen
  e <- expr
  tRParen
  return $ GenCallExpr ioqo ct e

----------------------------------------------------------------------
-- MISCELLANEOUS ELEMENTS
----------------------------------------------------------------------

-- TODO: monadify
-- Incompltete
ident :: Parser Ident
ident = do
  i <- tIdentifier
  return $ Ident i

identOrQuotedOp :: Parser IdentOrQuotedOp
identOrQuotedOp = IIdent <$> ident

annotations :: Parser Annotations
annotations = Annotations <$> many (tColonColon >> annotation)

annotation :: Parser Annotation
annotation = do
  eah <- exprAtomHead
  eat <- exprAtomTail
  return $ Annotation eah eat

----------------------------------------------------------------------
-- PRIMITIVES
----------------------------------------------------------------------

tIntNumber :: Parser Int
tIntNumber =
  (\(TIntNumber i) -> i) <$> satisfy' (\k -> case k of
                                               TIntNumber {} -> True
                                               _ -> False)

tFloatNumber :: Parser Float
tFloatNumber =
  (\(TFloatNumber f) -> f) <$> satisfy' (\k -> case k of
                                                 TFloatNumber {} -> True
                                                 _ -> False)

tIdentifier :: Parser String
tIdentifier =
  (\(TIdentifier s) -> s) <$> satisfy' (\k -> case k of
                                                TIdentifier {} -> True
                                                _ -> False)

tString :: Parser String
tString =
  (\(TString s) -> s) <$> satisfy' (\k -> case k of
                                            TString {} -> True
                                            _ -> False)


simpleToken :: Token -> Parser Token
simpleToken tok = satisfy' (== tok)


tArray :: Parser Token
tArray = simpleToken TArray

tBool :: Parser Token
tBool = simpleToken TBool

tConstraint :: Parser Token
tConstraint = simpleToken TConstraint

tDiff :: Parser Token
tDiff = simpleToken TDiff

tDiv :: Parser Token
tDiv = simpleToken TDiv

tElse :: Parser Token
tElse = simpleToken TElse

tElseIf :: Parser Token
tElseIf = simpleToken TElseIf

tEndIf :: Parser Token
tEndIf = simpleToken TEndIf

tFalse :: Parser Token
tFalse = simpleToken TFalse

tFloat :: Parser Token
tFloat = simpleToken TFloat

tFunction :: Parser Token
tFunction = simpleToken TFunction

tIf :: Parser Token
tIf = simpleToken TIf

tIn :: Parser Token
tIn = simpleToken TIn

tInclude :: Parser Token
tInclude = simpleToken TInclude

tInt :: Parser Token
tInt = simpleToken TInt

tIntersect :: Parser Token
tIntersect = simpleToken TIntersect

tLet :: Parser Token
tLet = simpleToken TLet

tMaximize :: Parser Token
tMaximize = simpleToken TMaximize

tMinimize :: Parser Token
tMinimize = simpleToken TMinimize

tMod :: Parser Token
tMod = simpleToken TMod

tNot :: Parser Token
tNot = simpleToken TNot

tOf :: Parser Token
tOf = simpleToken TOf

tOutput :: Parser Token
tOutput = simpleToken TOutput

tPar :: Parser Token
tPar = simpleToken TPar

tPredicate :: Parser Token
tPredicate = simpleToken TPredicate

tSatisfy :: Parser Token
tSatisfy = simpleToken TSatisfy

tSet :: Parser Token
tSet = simpleToken TSet

tSolve :: Parser Token
tSolve = simpleToken TSolve

tSubset :: Parser Token
tSubset = simpleToken TSubset

tSuperset :: Parser Token
tSuperset = simpleToken TSuperset

tSymDiff :: Parser Token
tSymDiff = simpleToken TSymDiff

tThen :: Parser Token
tThen = simpleToken TThen

tTrue :: Parser Token
tTrue = simpleToken TTrue

tUnion :: Parser Token
tUnion = simpleToken TUnion

tVar :: Parser Token
tVar = simpleToken TVar

tWhere :: Parser Token
tWhere = simpleToken TWhere

tXor :: Parser Token
tXor = simpleToken TXor


tStmtEnd :: Parser Token
tStmtEnd = simpleToken TStmtEnd

tEq :: Parser Token
tEq = simpleToken TEq

tColon :: Parser Token
tColon = simpleToken TColon

tColonColon :: Parser Token
tColonColon = simpleToken TColonColon

tLParen :: Parser Token
tLParen = simpleToken TLParen

tRParen :: Parser Token
tRParen = simpleToken TRParen

tComma :: Parser Token
tComma = simpleToken TComma

tEllipsis :: Parser Token
tEllipsis = simpleToken TEllipsis

tLBracket :: Parser Token
tLBracket = simpleToken TLBracket

tRBracket :: Parser Token
tRBracket = simpleToken TRBracket

tEquivalence :: Parser Token
tEquivalence = simpleToken TEquivalence

tRImplies :: Parser Token
tRImplies = simpleToken TRImplies

tLImplies :: Parser Token
tLImplies = simpleToken TLImplies

tOr :: Parser Token
tOr = simpleToken TOr

tAnd :: Parser Token
tAnd = simpleToken TAnd

tLt :: Parser Token
tLt = simpleToken TLt

tGt :: Parser Token
tGt = simpleToken TGt

tLeq :: Parser Token
tLeq = simpleToken TLeq

tGeq :: Parser Token
tGeq = simpleToken TGeq

tEqEq :: Parser Token
tEqEq = simpleToken TEqEq

tNeq :: Parser Token
tNeq = simpleToken TNeq

tPlusPlus :: Parser Token
tPlusPlus = simpleToken TPlusPlus

tPlus :: Parser Token
tPlus = simpleToken TPlus

tMinus :: Parser Token
tMinus = simpleToken TMinus

tStar :: Parser Token
tStar = simpleToken TStar

tSlash :: Parser Token
tSlash = simpleToken TSlash

tLBrace :: Parser Token
tLBrace = simpleToken TLBrace

tRBrace :: Parser Token
tRBrace = simpleToken TRBrace

tBar :: Parser Token
tBar = simpleToken TBar

tLBracketBar :: Parser Token
tLBracketBar = simpleToken TLBracketBar

tBarRBracket :: Parser Token
tBarRBracket = simpleToken TBarRBracket

----------------------------------------------------------------------
-- UTILS
----------------------------------------------------------------------

inTParen :: Parser a -> Parser a
inTParen = between tLParen tRParen

inTBracket :: Parser a -> Parser a
inTBracket = between tLBracket tRBracket

inTBrace :: Parser a -> Parser a
inTBrace = between tLBrace tRBrace

separated1 :: Parser Token -> Parser a -> Parser [a]
separated1 tkn parser = do
  el <- parser
  els <- try (tkn >> separated1 tkn parser) <|> return []
  return $ el:els

separated :: Parser Token -> Parser a -> Parser [a]
separated tkn parser = try (separated1 tkn parser) <|> return []
