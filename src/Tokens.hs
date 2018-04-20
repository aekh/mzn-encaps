module Tokens where

type Tokens = [Token]

data Token =
  TIntNumber Int
  | TFloatNumber Float
  | TIdentifier String
  | TString String

    -- KEYWORDS --

--  | TAnn
--  | TAnnotation
--  | TAny
  | TArray
  | TBool
--  | TCase
  | TConstraint
  | TDiff
  | TDiv
  | TElse
  | TElseIf
  | TEndIf
--  | TEnum
  | TFalse
  | TFloat
  | TFunction
  | TIf
  | TIn
  | TInclude
  | TInt
  | TIntersect
  | TLet
--  | TList
  | TMaximize
  | TMinimize
  | TMod
  | TNot
  | TOf
--  | TOp
--  | TOpt
  | TOutput
  | TPar
  | TPredicate
--  | TRecord
  | TSatisfy
  | TSet
  | TSolve
--  | TString
  | TSubset
  | TSuperset
  | TSymDiff
--  | TTest
  | TThen
  | TTrue
--  | TTuple
--  | TType
  | TUnion
  | TVar
  | TWhere
  | TXor

    -- SYMBOLS --

  | TStmtEnd
  | TEq
  | TColon
  | TColonColon
  | TLParen
  | TRParen
  | TComma
  | TEllipsis
  | TLBracket
  | TRBracket
  | TEquivalence
  | TRImplies
  | TLImplies
  | TOr
  | TAnd
  | TLt
  | TGt
  | TLeq
  | TGeq
  | TEqEq
  | TNeq
  | TPlusPlus
  | TPlus
  | TMinus
  | TStar
  | TSlash
  | TLBrace
  | TRBrace
  | TBar
  | TLBracketBar
  | TBarRBracket
--  | TQuote
  deriving (Eq)

instance Show Token where
  show (TIntNumber i) = show i
  show (TFloatNumber f) = show f
  show (TIdentifier s) = s
  show (TString s) = show s

  -- KEYWORDS --

--  show TAnn = "ann"
--  show TAnnotation = "annotation"
--  show TAny = "any"
  show TArray = "array"
  show TBool = "bool"
--  show TCase = "case"
  show TConstraint = "constraint"
  show TDiff = "diff"
  show TDiv = "div"
  show TElse = "else"
  show TElseIf = "elseif"
  show TEndIf = "endif"
--  show TEnum = "enum"
  show TFalse = "false"
  show TFloat = "float"
  show TFunction = "function"
  show TIf = "if"
  show TIn = "in"
  show TInclude = "include"
  show TInt = "int"
  show TIntersect = "intersect"
  show TLet = "let"
--  show TList = "list"
  show TMaximize = "maximize"
  show TMinimize = "minimize"
  show TMod = "mod"
  show TNot = "not"
  show TOf = "of"
--  show TOp = "op"
--  show TOpt = "opt"
  show TOutput = "output"
  show TPar = "par"
  show TPredicate = "predicate"
--  show TRecord = "record"
  show TSatisfy = "satisfy"
  show TSet = "set"
  show TSolve = "solve"
--  show TString = "string"
  show TSubset = "subset"
  show TSuperset = "superset"
  show TSymDiff = "symdiff"
--  show TTest = "test"
  show TThen = "then"
  show TTrue = "true"
--  show TTuple = "tuple"
--  show TType = "type"
  show TUnion = "union"
  show TVar = "var"
  show TWhere = "where"
  show TXor = "xor"

  -- SYMBOLS --

  show TStmtEnd = ";"
  show TEq = "="
  show TColon = ":"
  show TColonColon = "::"
  show TLParen = "("
  show TRParen = ")"
  show TComma = ","
  show TEllipsis = ".."
  show TLBracket = "["
  show TRBracket = "]"
  show TEquivalence = "<->"
  show TRImplies = "->"
  show TLImplies = "<-"
  show TOr = "\\/"
  show TAnd = "/\\"
  show TLt = "<"
  show TGt = ">"
  show TLeq = "<="
  show TGeq = ">="
  show TEqEq = "=="
  show TNeq = "!="
  show TPlusPlus = "++"
  show TPlus = "+"
  show TMinus = "-"
  show TStar = "*"
  show TSlash = "/"
  show TLBrace = "{"
  show TRBrace = "}"
  show TBar = "|"
  show TLBracketBar = "[|"
  show TBarRBracket = "|]"
--  show TQuote = "\""

isKeyword :: String -> Bool
isKeyword str = let
  kws = ["ann", "annotation", "any", "array",
         "bool",
         "case", "constraint",
         "diff", "div",
         "else", "elseif", "endif", "enum",
         "false", "float", "function",
         "if", "in", "include", "int", "instersect",
         "let", "list",
         "maximize", "minimize",
         "mod", "not",
         "of", "op", "output",
         "par", "predicate",
         "record",
         "satisfy", "set", "solve", "string", "subset", "superset", "symdiff",
         "test", "then", "true", "tuple", "type",
         "union",
         "var",
         "where",
         "xor"]
  in
   str `elem` kws
