{-|
A concrete syntax tree (CST) representing a reduced MiniZinc grammar
-}
module CST where

import Data.List (nub, (\\))

import Tokens

type CST = Model

----------------------------------------------------------------------
-- ITEMS
----------------------------------------------------------------------

newtype Model = Model [Item]
              deriving (Eq)

-- Incomplete: FlatZinc-complete
data Item = IIncludeItem IncludeItem
          | IVarDeclItem VarDeclItem
          | IAssignItem AssignItem
          | IConstraintItem ConstraintItem
          | ISolveItem SolveItem
          | IOutputItem OutputItem
          | IPredicateItem PredicateItem
--          | ITestItem
          | IFunctionItem FunctionItem
--          | IAnnotationItem
          deriving (Eq)

data TiExprAndId = TiExprAndId TiExpr Ident
                 deriving (Eq)

newtype IncludeItem = IncludeItem StringLiteral
                    deriving (Eq)

data VarDeclItem = VarDeclItem TiExprAndId Annotations (Maybe Expr)
                 deriving (Eq)

data AssignItem = AssignItem Ident Expr
                deriving (Eq)

newtype ConstraintItem = ConstraintItem Expr
                       deriving (Eq)

data SolveItem = SSatisfy Annotations
               | SMinimize Annotations Expr
               | SMaximize Annotations Expr
               deriving (Eq)

newtype OutputItem = OutputItem Expr
                   deriving (Eq)

newtype PredicateItem = PredicateItem OperationItemTail
                      deriving (Eq)

data FunctionItem = FunctionItem TiExpr OperationItemTail
                  deriving (Eq)

data OperationItemTail = OperationItemTail Ident Params Annotations (Maybe Expr)
                       deriving (Eq)

newtype Params = Params [TiExprAndId]
               deriving (Eq)

----------------------------------------------------------------------
-- TYPE-INST EXPRESSIONS
----------------------------------------------------------------------

data TiExpr = TiExpr BaseTiExpr
            deriving (Eq)

data BaseTiExpr = BaseTiExpr VarPar BaseTiExprTail
                deriving (Eq)

data VarPar = Var | Par
            deriving (Eq)

-- Incomplete: FlatZinc-complete
-- NOTE: no way to form `var {1} union 3..10: x; via spec,
--       added BExpr6 case for set expressions
-- TODO: Fix parser to parse EExpr6 stuff?
data BaseTiExprTail = BIdent Ident
                    | BBool
                    | BInt
                    | BFloat
                    | BSetTiExprTail SetTiExprTail
                    | BArrayTiExprTail ArrayTiExprTail
                    | BSet [Expr]
                    | BRange NumExpr NumExpr
                    | BExpr6 Expr6
                    deriving (Eq)

-- TODO base-type in docs
data SetTiExprTail = SInt
                   | SSet [Expr]
                   | SRange NumExpr NumExpr
                   | SExpr6 Expr6
                   deriving (Eq)

data ArrayTiExprTail = ArrayTiExprTail [TiExpr] TiExpr
                     deriving (Eq)

----------------------------------------------------------------------
-- EXPRESSIONS
----------------------------------------------------------------------

data Expr = Expr Expr12
          deriving (Eq)

data Expr12 = EEquivalence Expr12 Expr11
            | EExpr11 Expr11
            deriving (Eq)

data Expr11 = ERImplies Expr11 Expr10
            | ELImplies Expr11 Expr10
            | EExpr10 Expr10
            deriving (Eq)

data Expr10 = EOr Expr10 Expr9
            | EXor Expr10 Expr9
            | EExpr9 Expr9
            deriving (Eq)

data Expr9 = EAnd Expr9 Expr8
           | EExpr8 Expr8
           deriving (Eq)


data Expr8 = ELt Expr7 Expr7
           | EGt Expr7 Expr7
           | ELeq Expr7 Expr7
           | EGeq Expr7 Expr7
           | EEqEq Expr7 Expr7
           | EEq Expr7 Expr7
           | ENeq Expr7 Expr7
           | EExpr7 Expr7
           deriving (Eq)

data Expr7 = EIn Expr6 Expr6
           | ESubset Expr6 Expr6
           | ESuperset Expr6 Expr6
           | EExpr6 Expr6
           deriving (Eq)

data Expr6 = EUnion Expr6 Expr5
           | EDiff Expr6 Expr5
           | ESymDiff Expr6 Expr5
           | EExpr5 Expr5
           deriving (Eq)

data Expr5 = EEllipsis Expr4 Expr4
           | EExpr4 Expr4
           deriving (Eq)

data Expr4 = EPlus Expr4 Expr3
           | EMinus Expr4 Expr3
           | EExpr3 Expr3
           deriving (Eq)

data Expr3 = EStar Expr3 Expr2
           | EDiv Expr3 Expr2
           | EMod Expr3 Expr2
           | ESlash Expr3 Expr2
           | EIntersect Expr3 Expr2
           | EExpr2 Expr2
           deriving (Eq)

data Expr2 = EPlusPlus Expr1 Expr2
           | EExpr1 Expr1
           deriving (Eq)

data Expr1 = EIdent Ident Expr1 ExprAtom
           | EExprAtom ExprAtom
           deriving (Eq)

data ExprAtom = ExprAtom ExprAtomHead ExprAtomTail Annotations
              deriving (Eq)

-- Incomplete
data ExprAtomHead = EBuiltinUnOp BuiltinUnOp ExprAtom
                  | EExpr Expr
                  | EIdentOrQuotedOp IdentOrQuotedOp
                  | EBoolLiteral BoolLiteral
                  | EIntLiteral IntLiteral
                  | EFloatLiteral FloatLiteral
                  | EStringLiteral StringLiteral
                  | ESetLiteral SetLiteral
                  | ESetComp SetComp
                  | EArrayLiteral ArrayLiteral
                  | EArrayLiteral2d ArrayLiteral2d
                  | EArrayComp ArrayComp
                  | EIfThenElseExpr IfThenElseExpr
                  | ELetExpr LetExpr
                  | ECallExpr CallExpr
                  | EGenCallExpr GenCallExpr
                  deriving (Eq)

-- Incomplete
data ExprAtomTail = EATNothing
                  | ExprAtomTail ArrayAccessTail ExprAtomTail
                  deriving (Eq)

data NumExpr = NumExpr NumExpr4
             deriving (Eq)

data NumExpr4 = NPlus NumExpr4 NumExpr3
              | NMinus NumExpr4 NumExpr3
              | NNumExpr3 NumExpr3
              deriving (Eq)

data NumExpr3 = NStar NumExpr3 NumExpr1
              | NDiv NumExpr3 NumExpr1
              | NMod NumExpr3 NumExpr1
              | NSlash NumExpr3 NumExpr1
              | NNumExpr1 NumExpr1
              deriving (Eq)

data NumExpr1 = NIdent Ident NumExpr1 NumExprAtom
              | NNumExprAtom NumExprAtom
              deriving (Eq)

data NumExprAtom = NumExprAtom NumExprAtomHead ExprAtomTail Annotations
                 deriving (Eq)

-- Incomplete
data NumExprAtomHead = NBuiltinNumUnOp BuiltinNumUnOp NumExprAtom
                     | NNumExpr NumExpr
                     | NIdentOrQuotedOp IdentOrQuotedOp
                     | NIntLiteral IntLiteral
                     | NFloatLiteral FloatLiteral
                     | NIfThenElseExpr IfThenElseExpr
                     | NLetExpr LetExpr
                     | NCallExpr CallExpr
                     | NGenCallExpr GenCallExpr
                     deriving (Eq)

data BuiltinUnOp = BNot
                 | BBuiltinNumUnOp BuiltinNumUnOp
                 deriving (Eq)

data BuiltinNumUnOp = BPositive
                    | BNegative
                    deriving (Eq)

newtype BoolLiteral = BoolLiteral Bool
                    deriving (Eq)

newtype IntLiteral = IntLiteral Int
                   deriving (Eq)

newtype FloatLiteral = FloatLiteral Float
                     deriving (Eq)

-- TODO: Not equivalent to MiniZinc grammar
newtype StringLiteral = StringLiteral String
                      deriving (Eq)

newtype SetLiteral = SetLiteral [Expr]
                   deriving (Eq)

data SetComp = SetComp Expr CompTail
             deriving (Eq)

data CompTail = CompTail [Generator] (Maybe Expr)
              deriving (Eq)

data Generator = Generator [Ident] Expr
               deriving (Eq)

newtype ArrayLiteral = ArrayLiteral [Expr]
                     deriving (Eq)

data ArrayComp = ArrayComp Expr CompTail
               deriving (Eq)

newtype ArrayLiteral2d = ArrayLiteral2d [[Expr]]
                       deriving (Eq)

newtype ArrayAccessTail = ArrayAccessTail [Expr]
                        deriving (Eq)

data IfThenElseExpr = IfThenElseExpr Expr Expr [(Expr, Expr)] Expr
                    deriving (Eq)

data CallExpr = CallExpr IdentOrQuotedOp [Expr]
              deriving (Eq)

data LetExpr = LetExpr [LetItem] Expr
             deriving (Eq)

data LetItem = LVarDeclItem VarDeclItem
             | LConstraintItem ConstraintItem
             deriving (Eq)

data GenCallExpr = GenCallExpr IdentOrQuotedOp CompTail Expr
                 deriving (Eq)

----------------------------------------------------------------------
-- MISCELLANEOUS ELEMENTS
----------------------------------------------------------------------

data Ident = Ident String
           deriving (Eq)

-- Incomplete: FlatZinc-complete
data IdentOrQuotedOp = IIdent Ident
--                     | IBuiltinOp BuiltinOp
                     deriving (Eq)

data Annotations = Annotations [Annotation]
                 deriving (Eq)

data Annotation = Annotation ExprAtomHead ExprAtomTail
                deriving (Eq)

----------------------------------------------------------------------
-- FUNCTIONS
----------------------------------------------------------------------

conjunctConstraints :: [ConstraintItem] -> ConstraintItem
conjunctConstraints cis =
  let exprs = map (\(ConstraintItem e) -> e) cis
  in ConstraintItem $ foldl1 conjunction exprs

class Exprs e where;
instance Exprs Expr where;
instance Exprs Expr12 where;
instance Exprs Expr11 where;
instance Exprs Expr10 where;
instance Exprs Expr9 where;
instance Exprs Expr8 where;
instance Exprs Expr7 where;
instance Exprs Expr6 where;
instance Exprs Expr5 where;
instance Exprs Expr4 where;
instance Exprs Expr3 where;
instance Exprs Expr2 where;
instance Exprs Expr1 where;
instance Exprs ExprAtom where;
instance Exprs ExprAtomHead where;

conjunction :: Expr -> Expr -> Expr
conjunction e1 e2 =
  let e1p = EExpr8 (EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr e1) EATNothing (Annotations []))))))))))
      e2p = EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr e2) EATNothing (Annotations [])))))))))
  in Expr (EExpr11 (EExpr10 (EExpr9 (EAnd e1p e2p))))

exprAtomToExpr :: ExprAtom -> Expr
exprAtomToExpr ea = Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom ea))))))))))))

makePred :: ConstraintItem -> String -> [VarDeclItem] -> [VarDeclItem]
         -> PredicateItem
makePred (ConstraintItem expr) name vdiParams vdiLocals =
  let i = Ident name
      teais = map (\(VarDeclItem teai _ _) -> teai) vdiParams
      p = Params teais
      a = Annotation (ECallExpr (CallExpr (IIdent (Ident "presolve")) [])) EATNothing
      anns = Annotations [a]
      lis = LVarDeclItem <$> vdiLocals
      le = LetExpr lis expr
      e = Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (ELetExpr le) EATNothing (Annotations []))))))))))))))
      oit = OperationItemTail i p anns (Just e)
  in PredicateItem oit

makeConstraintCall :: String -> [VarDeclItem] -> ConstraintItem
makeConstraintCall predName vdiParams =
  let ioqoPredName = IIdent (Ident predName)
      ioqoParams = map (\(VarDeclItem (TiExprAndId _ i) _ _) -> IIdent i) vdiParams
      exprParams = map (\x -> Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EIdentOrQuotedOp x) EATNothing (Annotations []))))))))))))))) ioqoParams
      call = Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 (EExpr5 (EExpr4 (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (ECallExpr (CallExpr ioqoPredName exprParams)) EATNothing (Annotations []))))))))))))))
  in ConstraintItem call

----------------------------------------------------------------------
-- SHOW INSTANCES
----------------------------------------------------------------------

commaSeparated :: Show a => [a] -> String
commaSeparated [] = ""
commaSeparated [x] = show x
commaSeparated (x:xs) = show x ++ show TComma ++ " " ++ commaSeparated xs

showArray2d :: Show a => [[a]] -> String
showArray2d [] = ""
showArray2d [xs] = commaSeparated xs
showArray2d (xs:xss) = commaSeparated xs ++ " " ++ show TBar ++ " "
                       ++ showArray2d xss

stmtEndSeparated :: Show a => [a] -> String
stmtEndSeparated [] = ""
stmtEndSeparated [x] = show x
stmtEndSeparated (x:xs) = show x ++ show TStmtEnd ++ " " ++ stmtEndSeparated xs

spaced :: String -> String
spaced s = " " ++ s ++ " "

showElseIfs :: Show a => [(a, a)] -> String
showElseIfs [] = ""
showElseIfs ((c, e):eis) =
  show TElseIf ++ spaced (show c) ++ show TThen ++ spaced (show e) ++
  showElseIfs eis

instance Show Model where
  show (Model []) = ""
  show (Model [i]) = show i ++ show TStmtEnd
  show (Model (i:is)) = show i ++ show TStmtEnd ++ "\n" ++ show (Model is)

instance Show Item where
  show (IIncludeItem ii) = show ii
  show (IVarDeclItem vdi) = show vdi
  show (IAssignItem ai) = show ai
  show (IConstraintItem ci) = show ci
  show (ISolveItem si) = show si
  show (IOutputItem oi) = show oi
  show (IPredicateItem pi) = show pi
  --show (ITestItem ti) = show ti
  show (IFunctionItem fi) = show fi
  --show (IAnnotationItem ai) = show ai

instance Show TiExprAndId where
  show (TiExprAndId te i) =
    show te ++ show TColon ++ " " ++ show i

instance Show IncludeItem where
  show (IncludeItem sl) = show TInclude ++ " " ++ show sl

instance Show VarDeclItem where
  show (VarDeclItem teai a Nothing) =
    show teai ++ show a
  show (VarDeclItem teai a (Just e)) =
    show teai ++ show a ++ " " ++ show TEq ++ " " ++ show e

instance Show AssignItem where
  show (AssignItem i e) =
    show i ++ " " ++ show TEq ++ " " ++ show e

instance Show ConstraintItem where
  show (ConstraintItem e) =
    show TConstraint ++ " " ++ show e

instance Show SolveItem where
  show (SSatisfy a) =
    show TSolve ++ show a ++ " " ++ show TSatisfy
  show (SMinimize a e) =
    show TSolve ++ show a ++ " " ++ show TMinimize ++ " " ++ show e
  show (SMaximize a e) =
    show TSolve ++ show a ++ " " ++ show TMaximize ++ " " ++ show e

instance Show OutputItem where
  show (OutputItem e) = show TOutput ++ " " ++ show e

instance Show PredicateItem where
  show (PredicateItem oit) =
    show TPredicate ++ " " ++ show oit

instance Show FunctionItem where
  show (FunctionItem ti oit) =
    show TFunction ++ spaced (show ti) ++ show TColon ++ spaced (show oit)

instance Show OperationItemTail where
  show (OperationItemTail i p a Nothing) =
    show i ++ show p ++ show a
  show (OperationItemTail i p a (Just e)) =
    show i ++ show p ++ show a ++ " " ++ show TEq ++ " " ++ show e

instance Show Params where
  show (Params teais) =
    show TLParen ++ commaSeparated teais ++ show TRParen

instance Show TiExpr where
  show (TiExpr bte) = show bte

instance Show BaseTiExpr where
  show (BaseTiExpr vp btet) = show vp  ++ show btet

instance Show VarPar where
  show Var = show TVar ++ " "
  show Par = ""

instance Show BaseTiExprTail where
  show (BIdent i) = show i
  show BBool = show TBool
  show BInt = show TInt
  show BFloat = show TFloat
  show (BSetTiExprTail stet) = show stet
  show (BArrayTiExprTail atet) = show atet
  show (BSet es) =
    show TLBrace ++ commaSeparated es ++ show TRBrace
  show (BRange ne1 ne2) =
    show ne1 ++ show TEllipsis ++ show ne2

instance Show SetTiExprTail where
  show SInt =
    show TSet ++ " " ++ show TOf ++ " " ++ show TInt
  show (SSet es) =
    show TSet ++ " " ++ show TOf ++ " " ++
    show TLBrace ++ commaSeparated es ++ show TRBrace
  show (SRange ne1 ne2) =
    show TSet ++ " " ++ show TOf ++ " " ++
    show ne1 ++ show TEllipsis ++ show ne2
  show (SExpr6 e) = show e

instance Show ArrayTiExprTail where
  show (ArrayTiExprTail tes te) =
    show TArray ++ " " ++ show TLBracket ++
    commaSeparated tes ++
    show TRBracket ++ " " ++ show TOf ++ " " ++
    show te

instance Show Expr where
  show (Expr e) = show e

showp :: Show a => a -> String
showp x = "{" ++ show x ++ "}"

instance Show Expr12 where
  show (EEquivalence e1 e2) = show e1 ++ spaced (show TEquivalence) ++ show e2
  show (EExpr11 e) = show e

instance Show Expr11 where
  show (ERImplies e1 e2) = show e1 ++ spaced (show TRImplies) ++ show e2
  show (ELImplies e1 e2) = show e1 ++ spaced (show TLImplies) ++ show e2
  show (EExpr10 e) = show e

instance Show Expr10 where
  show (EOr e1 e2) = show e1 ++ spaced (show TOr) ++ show e2
  show (EXor e1 e2) = show e1 ++ spaced (show TXor) ++ show e2
  show (EExpr9 e) = show e

instance Show Expr9 where
  show (EAnd e1 e2) = show e1 ++ spaced (show TAnd) ++ show e2
  show (EExpr8 e) = show e

instance Show Expr8 where
  show (ELt e1 e2) = show e1 ++ spaced (show TLt) ++ show e2
  show (EGt e1 e2) = show e1 ++ spaced (show TGt) ++ show e2
  show (ELeq e1 e2) = show e1 ++ spaced (show TLeq) ++ show e2
  show (EGeq e1 e2) = show e1 ++ spaced (show TGeq) ++ show e2
  show (EEqEq e1 e2) = show e1 ++ spaced (show TEqEq) ++ show e2
  show (EEq e1 e2) = show e1 ++ spaced (show TEq) ++ show e2
  show (ENeq e1 e2) = show e1 ++ spaced (show TNeq) ++ show e2
  show (EExpr7 e) = show e

instance Show Expr7 where
  show (EIn e1 e2) = show e1 ++ spaced (show TIn) ++ show e2
  show (ESubset e1 e2) = show e1 ++ spaced (show TSubset) ++ show e2
  show (ESuperset e1 e2) = show e1 ++ spaced (show TSuperset) ++ show e2
  show (EExpr6 e) = show e

instance Show Expr6 where
  show (EUnion e1 e2) = show e1 ++ spaced (show TUnion) ++ show e2
  show (EDiff e1 e2) = show e1 ++ spaced (show TDiff) ++ show e2
  show (ESymDiff e1 e2) = show e1 ++ spaced (show TSymDiff) ++ show e2
  show (EExpr5 e) = show e

instance Show Expr5 where
  show (EEllipsis e1 e2) = show e1 ++ spaced (show TEllipsis) ++ show e2
  show (EExpr4 e) = show e

instance Show Expr4 where
  show (EPlus e1 e2) = show e1 ++ spaced (show TPlus) ++ show e2
  show (EMinus e1 e2) = show e1 ++ spaced (show TMinus) ++ show e2
  show (EExpr3 e) = show e

instance Show Expr3 where
  show (EStar e1 e2) = show e1 ++ spaced (show TStar) ++ show e2
  show (EDiv e1 e2) = show e1 ++ spaced (show TDiv) ++ show e2
  show (EMod e1 e2) = show e1 ++ spaced (show TMod) ++ show e2
  show (ESlash e1 e2) = show e1 ++ spaced (show TSlash) ++ show e2
  show (EIntersect e1 e2) = show e1 ++ spaced (show TIntersect) ++ show e2
  show (EExpr2 e) = show e

instance Show Expr2 where
  show (EPlusPlus e1 e2) = show e1 ++ spaced (show TPlusPlus) ++ show e2
  show (EExpr1 e) = show e

instance Show Expr1 where
  show (EIdent i e1 e2) = show e1 ++ spaced (show i) ++ show e2 -- TODO: Fix quotes
  show (EExprAtom ea) = show ea

instance Show ExprAtom where
  show (ExprAtom eah eat a) = show eah ++ show eat ++ show a

instance Show ExprAtomHead where
  show (EBuiltinUnOp buo ea) = show buo ++ show ea
  show (EExpr e) = show TLParen ++ show e ++ show TRParen
  show (EIdentOrQuotedOp ioqo) = show ioqo
  show (EBoolLiteral bl) = show bl
  show (EIntLiteral il) = show il
  show (EFloatLiteral fl) = show fl
  show (ESetLiteral sl) = show sl
  show (EStringLiteral sl) = show sl
  show (ESetComp sc) = show sc
  show (EArrayLiteral al) = show al
  show (EArrayLiteral2d al) = show al
  show (EArrayComp ac) = show ac
  show (EIfThenElseExpr itee) = show itee
  show (ELetExpr le) = show le
  show (ECallExpr ce) = show ce
  show (EGenCallExpr gce) = show gce

instance Show ExprAtomTail where
  show (ExprAtomTail aat eat) = show aat ++ show eat
  show _ = ""

instance Show NumExpr where
  show (NumExpr ne) = show ne

instance Show NumExpr4 where
  show (NPlus ne1 ne2) = show ne1 ++ spaced (show TPlus) ++ show ne2
  show (NMinus ne1 ne2) = show ne1 ++ spaced (show TMinus) ++ show ne2
  show (NNumExpr3 ne) = show ne

instance Show NumExpr3 where
  show (NStar ne1 ne2) = show ne1 ++ spaced (show TStar) ++ show ne2
  show (NDiv ne1 ne2) = show ne1 ++ spaced (show TDiv) ++ show ne2
  show (NMod ne1 ne2) = show ne1 ++ spaced (show TMod) ++ show ne2
  show (NSlash ne1 ne2) = show ne1 ++ spaced (show TSlash) ++ show ne2
  show (NNumExpr1 ne) = show ne

instance Show NumExpr1 where
  show (NIdent i ne1 ne2) = show ne1 ++ spaced (show i) ++ show ne2 -- TODO: Fix quotes
  show (NNumExprAtom nea) = show nea

instance Show NumExprAtom where
  show (NumExprAtom neah eat a) = show neah ++ show eat ++ show a

instance Show NumExprAtomHead where
  show (NBuiltinNumUnOp bnuo nea) = show bnuo ++ show nea
  show (NNumExpr ne) = show TLParen ++ show ne ++ show TRParen
  show (NIdentOrQuotedOp ioqo) = show ioqo
  show (NIntLiteral il) = show il
  show (NFloatLiteral fl) = show fl
  show (NIfThenElseExpr itee) = show itee
  show (NLetExpr le) = show le
  show (NCallExpr ce) = show ce
  show (NGenCallExpr gce) = show gce

instance Show BuiltinUnOp where
  show BNot = show TNot ++ " "
  show (BBuiltinNumUnOp bnuo) = show bnuo

instance Show BuiltinNumUnOp where
  show BPositive = ""
  show BNegative = show TMinus

instance Show BoolLiteral where
  show (BoolLiteral True) = show TTrue
  show (BoolLiteral False) = show TFalse

instance Show IntLiteral where
  show (IntLiteral i) = show i

instance Show FloatLiteral where
  show (FloatLiteral f) = show f

instance Show StringLiteral where
  show (StringLiteral s) = show s

instance Show SetLiteral where
  show (SetLiteral es) =
    show TLBrace ++ commaSeparated es ++ show TRBrace

instance Show SetComp where
  show (SetComp e ct) =
    show TLBrace ++ show e ++ spaced (show TBar) ++ show ct ++ show TRBrace

instance Show CompTail where
  show (CompTail gs Nothing) = commaSeparated gs
  show (CompTail gs (Just e)) =
    commaSeparated gs ++ spaced (show TWhere) ++ show e

instance Show Generator where
  show (Generator is e) = commaSeparated is ++ spaced (show TIn) ++ show e

instance Show ArrayLiteral where
  show (ArrayLiteral es) = show TLBracket ++ commaSeparated es ++ show TRBracket

instance Show ArrayLiteral2d where
  show (ArrayLiteral2d ess) =
    show TLBracketBar ++ showArray2d ess ++ show TBarRBracket

instance Show ArrayComp where
  show (ArrayComp e ct) =
    show TLBracket ++ show e ++ spaced (show TBar) ++ show ct ++ show TRBracket

instance Show ArrayAccessTail where
  show (ArrayAccessTail es) =
    show TLBracket ++ commaSeparated es ++ show TRBracket

instance Show IfThenElseExpr where
  show (IfThenElseExpr c e ces ee) =
    show TIf ++ spaced (show c) ++ show TThen ++ spaced (show e) ++
    showElseIfs ces ++ show TElse ++ spaced (show ee) ++ show TEndIf

instance Show CallExpr where
  show (CallExpr ioqo es) =
    show ioqo ++ show TLParen ++
    commaSeparated es ++
    show TRParen

instance Show LetExpr where
  show (LetExpr lis e) =
    show TLet ++
    spaced (show TLBrace ++ stmtEndSeparated lis ++ show TRBrace) ++
    show TIn ++ " " ++ show e

instance Show LetItem where
  show (LVarDeclItem vdi) = show vdi
  show (LConstraintItem ci) = show ci

instance Show GenCallExpr where
  show (GenCallExpr ioqo ct e) =
    show ioqo ++ show TLParen ++ show ct ++ show TRParen ++
    show TLParen ++ show e ++ show TRParen

instance Show Ident where
  show (Ident s) = s

instance Show IdentOrQuotedOp where
  show (IIdent i) = show i

instance Show Annotations where
  show (Annotations []) = ""
  show (Annotations (a:as)) =
    " " ++ show TColonColon ++ " " ++ show a ++ show (Annotations as)

instance Show Annotation where
  show (Annotation eah eat) = show eah ++ show eat

----------------------------------------------------------------------
-- Identifiers
----------------------------------------------------------------------

class Identifiers a where
  identifiers :: a -> [Ident]
  locals :: a -> [Ident]
  locals _ = []

concatMapTuple :: (a -> [b]) -> (a, a) -> [b]
concatMapTuple f (x, y) = f x ++ f y

instance Identifiers SolveItem where
  identifiers (SSatisfy _) = []
  identifiers (SMaximize _ e) = identifiers e
  identifiers (SMinimize _ e) = identifiers e

instance Identifiers VarDeclItem where
  identifiers _ = [] -- TODO NumExpr!
  locals (VarDeclItem (TiExprAndId _ i) _ _) = [i]

instance Identifiers Expr where
  identifiers (Expr e) = identifiers e
  locals (Expr e) = locals e

instance Identifiers Expr12 where
  identifiers (EEquivalence e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr11 e) = identifiers e
  locals (EExpr11 e) = locals e
  locals _ = []

instance Identifiers Expr11 where
  identifiers (ERImplies e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ELImplies e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr10 e) = identifiers e
  locals (EExpr10 e) = locals e
  locals _ = []

instance Identifiers Expr10 where
  identifiers (EOr e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EXor e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr9 e) = identifiers e
  locals (EExpr9 e) = locals e
  locals _ = []

instance Identifiers Expr9 where
  identifiers (EAnd e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr8 e) = identifiers e
  locals (EExpr8 e) = locals e
  locals _ = []

instance Identifiers Expr8 where
  identifiers (ELt e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EGt e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ELeq e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EGeq e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EEqEq e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EEq e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ENeq e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr7 e) = identifiers e
  locals (EExpr7 e) = locals e
  locals _ = []

instance Identifiers Expr7 where
  identifiers (EIn e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ESubset e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ESuperset e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr6 e) = identifiers e
  locals (EExpr6 e) = locals e
  locals _ = []

instance Identifiers Expr6 where
  identifiers (EUnion e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EDiff e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ESymDiff e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr5 e) = identifiers e
  locals (EExpr5 e) = locals e
  locals _ = []

instance Identifiers Expr5 where
  identifiers (EEllipsis e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr4 e) = identifiers e
  locals (EExpr4 e) = locals e
  locals _ = []

instance Identifiers Expr4 where
  identifiers (EPlus e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EMinus e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr3 e) = identifiers e
  locals (EExpr3 e) = locals e
  locals _ = []

instance Identifiers Expr3 where
  identifiers (EStar e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EDiv e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EMod e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (ESlash e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EIntersect e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr2 e) = identifiers e
  locals (EExpr2 e) = locals e
  locals _ = []

instance Identifiers Expr2 where
  identifiers (EPlusPlus e1 e2) =
    nub (identifiers e1 ++ identifiers e2)
  identifiers (EExpr1 e) = identifiers e
  locals (EExpr1 e) = locals e
  locals _ = []

instance Identifiers Expr1 where
  identifiers (EIdent i e1 e2) =
    nub (identifiers i ++ identifiers e1 ++ identifiers e2)
  identifiers (EExprAtom ea) = identifiers ea
  locals (EExprAtom ea) = locals ea
  locals _ = []

instance Identifiers ExprAtom where
  identifiers (ExprAtom eah eat _) = nub (identifiers eah ++ identifiers eat)
  locals (ExprAtom eah eat _) = locals eah -- TODO: correct?

instance Identifiers ExprAtomHead where
  identifiers (EExpr e) = identifiers e
  identifiers (EIdentOrQuotedOp ioqo) = identifiers ioqo
  identifiers (ESetLiteral sl) = identifiers sl
  identifiers (ESetComp sc) = identifiers sc
  identifiers (EArrayLiteral al) = identifiers al
  identifiers (EArrayLiteral2d al) = identifiers al
  identifiers (EArrayComp ac) = identifiers ac
  identifiers (EIfThenElseExpr itee) = identifiers itee
  identifiers (ELetExpr le) = identifiers le
  identifiers (ECallExpr ce) = identifiers ce
  identifiers (EGenCallExpr gce) = identifiers gce
  identifiers _ = []
  locals (EExpr e) = locals e
  locals (EIdentOrQuotedOp ioqo) = locals ioqo
  locals (ESetLiteral sl) = locals sl
  locals (ESetComp sc) = locals sc
  locals (EArrayLiteral al) = locals al
  locals (EArrayComp ac) = locals ac
  locals (EIfThenElseExpr itee) = locals itee
  locals (ELetExpr le) = locals le
  locals (ECallExpr ce) = locals ce
  locals (EGenCallExpr gce) = locals gce
  locals _ = []

instance Identifiers ExprAtomTail where
  identifiers (ExprAtomTail aat eat) =
    nub (identifiers aat ++ identifiers eat)
  identifiers _ = []
  locals _ = []

instance Identifiers NumExpr where
  identifiers (NumExpr ne) = identifiers ne
  locals _ = []

instance Identifiers NumExpr4 where
  identifiers (NPlus ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NMinus ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NNumExpr3 ne) = identifiers ne
  locals _ = []

instance Identifiers NumExpr3 where
  identifiers (NStar ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NDiv ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NMod ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NSlash ne1 ne2) =
    nub (identifiers ne1 ++ identifiers ne2)
  identifiers (NNumExpr1 ne) = identifiers ne
  locals _ = []

instance Identifiers NumExpr1 where
  identifiers (NIdent i ne1 ne2) =
    nub (identifiers i ++ identifiers ne1 ++ identifiers ne2)
  identifiers (NNumExprAtom nea) = identifiers nea
  locals _ = []

instance Identifiers NumExprAtom where
  identifiers (NumExprAtom neah eat _) =
    nub (identifiers neah ++ identifiers eat)
  locals _ = []

instance Identifiers NumExprAtomHead where
  identifiers (NNumExpr ne) = identifiers ne
  identifiers (NIdentOrQuotedOp ioqo) = identifiers ioqo
  identifiers (NIfThenElseExpr itee) = identifiers itee
  identifiers (NLetExpr le) = identifiers le
  identifiers (NCallExpr ce) = identifiers ce
  identifiers (NGenCallExpr gce) = identifiers gce
  identifiers _ = []
  locals _ = [] -- TODO: is this correct?

instance Identifiers SetLiteral where
  identifiers (SetLiteral es) = nub $ concatMap identifiers es
  locals _ = []

instance Identifiers SetComp where
  identifiers sc@(SetComp e ct) =
    nub (identifiers e ++ identifiers ct) \\ locals sc
  locals (SetComp _ ct) = locals ct

instance Identifiers CompTail where -- TODO: how to handle locals?
  identifiers ct@(CompTail gs Nothing) =
    nub $ concatMap identifiers gs \\ locals ct
  identifiers ct@(CompTail gs (Just e)) =
    nub (concatMap identifiers gs ++ identifiers e) \\ locals ct
  locals (CompTail [] _) = []
  locals (CompTail (g : gs) e) =
    nub (locals g ++ locals (CompTail gs e))

instance Identifiers Generator where
  identifiers (Generator _ e) = identifiers e
  locals (Generator is _) = nub is

instance Identifiers ArrayLiteral where
  identifiers (ArrayLiteral es) = nub $ concatMap identifiers es
  locals _ = []

instance Identifiers ArrayLiteral2d where
  identifiers (ArrayLiteral2d ess) =
    nub $ concatMap (concatMap identifiers) ess
  locals _ = []

instance Identifiers ArrayComp where
  identifiers ac@(ArrayComp e ct) =
    nub (identifiers e ++ identifiers ct) \\ locals ac
  locals (ArrayComp _ ct) = locals ct

instance Identifiers ArrayAccessTail where
  identifiers (ArrayAccessTail es) = nub $ concatMap identifiers es
  locals _ = []

instance Identifiers IfThenElseExpr where
  identifiers (IfThenElseExpr c e ces ee) =
    let cesIds = concatMap (concatMapTuple identifiers) ces
    in nub (identifiers c ++ identifiers e ++ cesIds ++ identifiers ee)
  locals _ = []

instance Identifiers CallExpr where
  identifiers (CallExpr ioqo es) =
    nub $ concatMap identifiers es
  locals _ = []

instance Identifiers LetExpr where
  identifiers le@(LetExpr lis e) =
    identifiers e \\ locals le
  locals (LetExpr lis _) = nub (concatMap locals lis)

instance Identifiers LetItem where -- TODO!
  identifiers (LVarDeclItem vdi) = [] -- identifiers vdi
  identifiers (LConstraintItem ci) = []
  locals (LVarDeclItem vdi) = locals vdi
  locals _ = []

instance Identifiers GenCallExpr where
  identifiers (GenCallExpr _ ct e) =
    nub (identifiers ct ++ identifiers e) \\ locals ct
  locals (GenCallExpr _ ct _) = locals ct

instance Identifiers Ident where
  identifiers i = [i]
  locals _ = []

instance Identifiers IdentOrQuotedOp where
  identifiers (IIdent i) = identifiers i
  locals _ = []
