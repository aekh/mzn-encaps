{-| Formula Matching DAG -}
module FMD where

import Data.List (find, findIndex, delete, nub, elemIndex,)
import Text.Read (readMaybe)
import Data.Maybe (fromMaybe)

import CST
import CST.Utils (toBte, substitute)

import Debug.Trace

data FMD = FMD Environment [Vertex] [Edge]
         deriving (Eq, Show)

newtype Vertex = Vertex Expr
               deriving (Eq, Show)

data Edge = Edge Relation Int Int
          deriving (Eq, Show)

data Relation = Subformula
              | Generalisation
              | Abstraction
              deriving (Eq, Show)

data Declaration = Declaration BaseTiExpr Ident
                 deriving (Show, Eq) -- Define subtype

data Definition = Definition BaseTiExpr Ident [Declaration] (Maybe Expr)
                deriving (Show, Eq)

data Conversion = Conversion Ident Ident
                deriving (Show, Eq)

data Abstr = Abstr Expr Ident
                 deriving (Show, Eq)

data Environment = Environment [Declaration] [Definition]
                               [Conversion] [Abstr] SolveItem
                 deriving (Show, Eq)

fmdToItems :: FMD -> [Item]
fmdToItems (FMD _ vs es) =
  IConstraintItem . ConstraintItem <$> toConstraints vs es 0

toConstraints :: [Vertex] -> [Edge] -> Int -> [Expr]
toConstraints [] _ _ = []
toConstraints (Vertex e:vs) es i  =
  case find (\(Edge _ _ to) -> to == i) es of
    Nothing -> e : toConstraints vs es (i+1)
    Just _ -> toConstraints vs es (i+1)


emptySolveItem :: SolveItem
emptySolveItem = SSatisfy $ Annotations []

emptyEnv :: Environment
emptyEnv = Environment [] [] [] [] emptySolveItem

baseEnv :: Environment
baseEnv = Environment baseDecls baseDefs [] [] emptySolveItem

baseDecls :: [Declaration]
baseDecls = []

baseDefs :: [Definition]
baseDefs = [Definition (BaseTiExpr Var BBool) (Ident "forall") [] Nothing
           ,Definition (BaseTiExpr Var BBool) (Ident "exist") [] Nothing
           ,Definition (BaseTiExpr Var BBool) (Ident "alldifferent") [] Nothing
           ,Definition (BaseTiExpr Var BBool) (Ident "all_different") [] Nothing
           ,Definition (BaseTiExpr Var BBool) (Ident "cumulative") [] Nothing
           ,Definition (BaseTiExpr Var BBool) (Ident "diffn") [] Nothing
           ,Definition (BaseTiExpr Var BInt) (Ident "bool2int") [] Nothing
           ,Definition (BaseTiExpr Var BInt) (Ident "sum") [] Nothing
           ,Definition (BaseTiExpr Var BInt) (Ident "pow") [] Nothing
           ,Definition (BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail
                                         [TiExpr (BaseTiExpr Var BInt)]
                                         (TiExpr (BaseTiExpr Var BInt)))))
             (Ident "inverse") [] Nothing
           ]

insertDeclaration :: Declaration -> Environment -> Environment
insertDeclaration decl (Environment decls defs table abstrs si) =
  Environment (decl : decls) defs table abstrs si

insertDefinition :: Definition -> Environment -> Environment
insertDefinition def (Environment decls defs table abstrs si) =
  Environment decls (def : defs) table abstrs si

insertConversion :: Conversion -> Environment -> Environment
insertConversion conv (Environment decls defs convs abstrs si) =
  Environment decls defs (conv : convs) abstrs si

insertAbstr :: Abstr -> Environment -> Environment
insertAbstr abstr env@(Environment decls defs convs abstrs si) =
  case find (==abstr) abstrs of
    Nothing -> Environment decls defs convs (abstr : abstrs) si
    Just _ -> env

replaceSolveItem :: SolveItem -> Environment -> Environment
replaceSolveItem si' (Environment decls defs convs abstrs si) =
  Environment decls defs convs abstrs si'

mkDecl :: TiExprAndId -> Declaration
mkDecl (TiExprAndId (TiExpr bte) i) =
  Declaration bte i

mkEnv :: CST -> Environment
mkEnv (Model []) = baseEnv
mkEnv (Model (IVarDeclItem (VarDeclItem teai _ _):is)) =
  let decl = mkDecl teai
  in insertDeclaration decl $ mkEnv (Model is)
mkEnv (Model (IPredicateItem pi:is)) =
  let (PredicateItem (OperationItemTail i (Params teais) _ mExpr)) = pi
      decls = map mkDecl teais
      bte = BaseTiExpr Var BBool
      def = Definition bte i decls mExpr
  in insertDefinition def $ mkEnv (Model is)
mkEnv (Model (IFunctionItem fi:is)) =
  let (FunctionItem (TiExpr bte)
                    (OperationItemTail i (Params teais) _ mExpr)) = fi
      decls = map mkDecl teais
      def = Definition bte i decls mExpr
  in insertDefinition def $ mkEnv (Model is)
mkEnv (Model (ISolveItem si:is)) =
  replaceSolveItem si $ mkEnv (Model is)
mkEnv (Model (_:is)) = mkEnv (Model is)

--combineEnvs :: Environment -> Environment -> Environment
--combineEnvs (Environment decls1 defs1) (Environment decls2 defs2) =
--  Environment (nub $ decls1 ++ decls2) (nub $ defs1 ++ defs2)

findDef :: Environment -> Ident -> Maybe Definition
findDef (Environment _ defs _ _ _) i =
  find (\(Definition _ i' _ _) -> i' == i) defs

findDecl :: Environment -> Ident -> Maybe Declaration
findDecl (Environment decls _ _ _ _) i =
  find (\(Declaration _ i') -> i' == i) decls

findOrig :: Environment -> Ident -> Maybe Ident
findOrig (Environment _ _ convs _ _) i =
  case find (\(Conversion _ n) -> n == i) convs of
    Nothing -> Nothing
    Just (Conversion o _) -> Just o

findExpr :: Environment -> Ident -> Maybe Expr
findExpr (Environment _ _ _ abstrs _) i =
  case find (\(Abstr _ i') -> i' == i) abstrs of
    Nothing -> Nothing
    Just (Abstr e _) -> Just e

findAbstr :: Environment -> Expr -> Maybe Ident
findAbstr env@(Environment _ _ _ abstrs _) e =
  case find (\(Abstr e' _) -> equiv e' e env) abstrs of
    Nothing -> Nothing
    Just (Abstr _ i) -> Just i

findObjective :: Environment -> Maybe Expr
findObjective (Environment _ _ _ _ (SSatisfy _)) = Nothing
findObjective (Environment _ _ _ _ (SMinimize _ e)) = Just e
findObjective (Environment _ _ _ _ (SMaximize _ e)) = Just e

mSameType :: Maybe Declaration -> Maybe Declaration -> Bool
mSameType Nothing _ = False
mSameType _ Nothing = False
mSameType (Just (Declaration t1 _)) (Just (Declaration t2 _)) = t1 == t2

isBoolDecl :: Declaration -> Bool
isBoolDecl (Declaration (BaseTiExpr _ (BBool)) _) = True
isBoolDecl _ = False

isBoolDef :: Definition -> Bool
isBoolDef (Definition (BaseTiExpr _ (BBool)) _ _ _) = True
isBoolDef _ = False

class Freshify a where
  freshify :: [Expr] -> a -> Environment -> ([Expr], Environment)

instance Freshify CompTail where
  freshify [] _ env = ([], env)
  freshify (e : es) ct@(CompTail gs _) env =
    let (es', env') = freshify es ct env
        (e', env'') = foldl f (e, env') $ concatMap toDecl gs
    in {-trace ("Freshify CompTail -- exprs: " ++ show (e' : es') ++
              "\nfinal env: " ++ show env'')-} (e' : es', env'')
    where f :: (Expr, Environment) -> Declaration -> (Expr, Environment)
          f (expr, env) decl@(Declaration _ old) =
            let (env', new) = freshDecl env decl
            in (substitute expr old new [], env')

instance Freshify LetExpr where
  freshify [] _ env = ([], env)
  freshify (e : es) le@(LetExpr lis _) env =
    let (es', env') = freshify es le env
        (e', env'') = foldl f (e, env') $ concatMap toDecl lis
    in {-trace ("Freshify LetExpr -- exprs: " ++ show (e' : es') ++
              "\nfinal env: " ++ show env'')-} (e' : es', env'')
    where f :: (Expr, Environment) -> Declaration -> (Expr, Environment)
          f (expr, env) decl@(Declaration _ old) =
            let (env', new) = freshDecl env decl
            in (substitute expr old new [], env')

class ToDecl a where
  toDecl :: a -> [Declaration]

instance ToDecl Generator where
  toDecl (Generator [] _) = []
  toDecl (Generator (i:is) e) =
    Declaration (toBte e) i : toDecl (Generator is e)

instance ToDecl LetItem where
  toDecl (LVarDeclItem (VarDeclItem teai _ _)) =
    [mkDecl teai]
  toDecl _ = []

freshDecl :: Environment -> Declaration -> (Environment, Ident)
freshDecl (Environment decls defs convs abstrs si)
          (Declaration t@(BaseTiExpr Var _) (Ident "ADUMMY")) =
  let freshIdent = Ident $ freshDecl' decls "AbV_" [True]
      fresh = Declaration t freshIdent
  in (Environment (fresh : decls) defs convs abstrs si, freshIdent)
freshDecl (Environment decls defs convs abstrs si)
          (Declaration t@(BaseTiExpr Par _) (Ident "ADUMMY")) =
  let freshIdent = Ident $ freshDecl' decls "AbN_" [True]
      fresh = Declaration t freshIdent
  in (Environment (fresh : decls) defs convs abstrs si, freshIdent)
freshDecl (Environment decls defs convs abstrs si)
          (Declaration t@(BaseTiExpr Var _) i) =
  let freshIdent = Ident $ freshDecl' decls "V_" [True]
      fresh = Declaration t freshIdent
      conv = Conversion i freshIdent
  in (Environment (fresh : decls) defs (conv : convs) abstrs si, freshIdent)
freshDecl (Environment decls defs convs abstrs si)
          (Declaration t@(BaseTiExpr Par _) i) =
  let freshIdent = Ident $ freshDecl' decls "N_" [True]
      fresh = Declaration t freshIdent
      conv = Conversion i freshIdent
  in (Environment (fresh : decls) defs (conv : convs) abstrs si, freshIdent)

freshDecl' :: [Declaration] -> String -> [Bool] -> String
freshDecl' [] name frees = let (Just pos) = elemIndex True frees
                           in name ++ show pos
freshDecl' (Declaration _ (Ident s):ds) name frees =
  case (prefix name s, readMaybe (drop (length name) s) :: Maybe Int) of
    (False, _) -> freshDecl' ds name frees
    (_, Nothing) -> freshDecl' ds name frees
    (True, Just suf) -> freshDecl' ds name (falseAt frees suf)

falseAt :: [Bool] -> Int -> [Bool]
falseAt [] i = replicate i True ++ [False] ++ [True]
falseAt [_] 0 = False : [True]
falseAt (_:bs) 0 = False : bs
falseAt (b:bs) i = b : falseAt bs (i-1)

prefix :: String -> String -> Bool
prefix [] _ = True
prefix (_:_) [] = False
prefix (x:xs) (y:ys) = (x == y) && prefix xs ys

emptyFMD :: Environment -> FMD
emptyFMD env = FMD env [] []

insertVertex :: FMD -> Vertex -> (FMD, Int, Bool)
insertVertex fmd@(FMD env vs es) v =
  case findIndex (\x -> equiv x v env) vs of
    Just i -> (fmd, i, False)
    Nothing -> (FMD env (vs ++ [v]) es, length vs, True)

insertEdge :: FMD -> Edge -> FMD
insertEdge fmd (Edge _ a b) | a == b = fmd
insertEdge (FMD env vs es) e =
  FMD env vs (e : es) -- defend against duplicates?

-------------------------
-- FORMULA EQUIVALENCE --
-------------------------

equivLists :: (Eq a, Formula a) => [a] -> [a] -> Environment -> Bool
equivLists [] [] env = True
equivLists [] _ env = False
equivLists _ [] env = False
equivLists (x:xs) ys env =
  case find (\a -> equiv x a env) ys of
    Just match -> equivLists xs (delete match ys) env
    Nothing -> False

equivTupleLists :: (Eq a, Eq b, Formula a, Formula b) =>
                   [(a,b)] -> [(a,b)] -> Environment -> Bool
equivTupleLists [] [] env = True
equivTupleLists [] _ env = False
equivTupleLists _ [] env = False
equivTupleLists ((x1,x2):xs) ys env =
  case find (\(a,b) -> equiv x1 a env && equiv x2 b env) ys of
    Just match -> equivTupleLists xs (delete match ys) env
    Nothing -> False

class Formula a where
  equiv :: a -> a -> Environment -> Bool

instance Formula Vertex where
  equiv (Vertex e1) (Vertex e2) = equiv e1 e2

instance Formula TiExprAndId where
  equiv (TiExprAndId (TiExpr (BaseTiExpr _ btet1)) _)
        (TiExprAndId (TiExpr (BaseTiExpr _ btet2)) _) =
    equiv btet1 btet2

instance Formula VarDeclItem where
  equiv (VarDeclItem teai1 i1 Nothing) (VarDeclItem teai2 i2 Nothing) env =
    i1 == i2 && equiv teai1 teai2 env
  equiv (VarDeclItem teai1 i1 (Just e1)) (VarDeclItem teai2 i2 (Just e2)) env =
    i1 == i2 && equiv teai1 teai2 env && equiv e1 e2 env
  equiv _ _ _ = False

instance Formula ConstraintItem where
  equiv (ConstraintItem e1) (ConstraintItem e2) = equiv e1 e2

instance Formula BaseTiExprTail where
  equiv (BIdent i1) (BIdent i2) env = equiv i1 i2 env
  equiv BBool BBool _ = True
  equiv BFloat BFloat _ = True
  equiv BInt BInt _ = True
  --formula (BSetTiExprTail stet) env = undefined
    -- BSetTiExprTail$ substitutePart stet env
  --formula (BArrayTiExprTail atet) env = undefined
    -- BArrayTiExprTail $ substitutePart atet env
  equiv (BSet es1) (BSet es2) env = equivLists es1 es2 env
  equiv (BRange ne11 ne12) (BRange ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (BExpr6 e1) (BExpr6 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr where
  equiv (Expr e1) (Expr e2) = equiv e1 e2

instance Formula Expr12 where
  equiv (EEquivalence e11 e12) (EEquivalence e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr11 e22) env && equiv (EExpr11 e12) e21 env)
  equiv (EExpr11 e1) (EExpr11 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr11 where
  equiv (ELImplies e11 e12) (ELImplies e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ERImplies e11 e12) (ERImplies e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ELImplies e11 e12) (ERImplies e21 e22) env =
    equiv e11 (EExpr10 e22) env && equiv (EExpr10 e12) e21 env
  equiv (ERImplies e11 e12) (ELImplies e21 e22) env =
    equiv e11 (EExpr10 e22) env && equiv (EExpr10 e12) e21 env
  equiv (EExpr10 e1) (EExpr10 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr10 where
  equiv (EOr e11 e12) (EOr e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr9 e22) env && equiv (EExpr9 e12) e21 env)
  equiv (EXor e11 e12) (EXor e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr9 e22) env && equiv (EExpr9 e12) e21 env)
  equiv (EExpr9 e1) (EExpr9 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr9 where
  equiv (EAnd e11 e12) (EAnd e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr8 e22) env && equiv (EExpr8 e12) e21 env)
  equiv (EExpr8 e1) (EExpr8 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr8 where
  equiv (EGt e11 e12) e env =
    equiv (ELt e12 e11) e env
  equiv e (EGt e11 e12) env =
    equiv e (ELt e12 e11) env
  equiv (EGeq e11 e12) e env =
    equiv (ELeq e12 e11) e env
  equiv e (EGeq e11 e12) env =
    equiv e (ELeq e12 e11) env
  equiv (EEqEq e11 e12) e env =
    equiv (EEq e12 e11) e env
  equiv e (EEqEq e11 e12) env =
    equiv e (EEq e12 e11) env

  equiv (ELt e11 e12) (ELt e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ELeq e11 e12) (ELeq e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EEq e11 e12) (EEq e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 e22 env && equiv e12 e21 env)
  equiv (ENeq e11 e12) (ENeq e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 e22 env && equiv e12 e21 env)
  equiv (EExpr7 e1) (EExpr7 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr7 where
  equiv (EIn e11 e12) (EIn e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ESubset e11 e12) (ESubset e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ESuperset e11 e12) (ESuperset e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EExpr6 e1) (EExpr6 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr6 where
  equiv (EUnion e11 e12) (EUnion e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr5 e22) env && equiv (EExpr5 e12) e21 env)
  equiv (EDiff e11 e12) (EDiff e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ESymDiff e11 e12) (ESymDiff e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr5 e22) env && equiv (EExpr5 e12) e21 env)
  equiv (EExpr5 e1) (EExpr5 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr5 where
  equiv (EEllipsis e11 e12) (EEllipsis e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EExpr4 e1) (EExpr4 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr4 where
  equiv (EPlus e11 e12) (EPlus e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr3 e22) env && equiv (EExpr3 e12) e21 env)
  equiv (EMinus e11 e12) (EMinus e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr3 e22) env && equiv (EExpr3 e12) e21 env)
  equiv (EExpr3 e1) (EExpr3 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr3 where
  equiv (EStar e11 e12) (EStar e21 e22) env =
    (equiv e11 e21 env && equiv e12 e22 env) ||
    (equiv e11 (EExpr2 e22) env && equiv (EExpr2 e12) e21 env)
  equiv (EDiv e11 e12) (EDiv e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EMod e11 e12) (EMod e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (ESlash e11 e12) (ESlash e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EIntersect e11 e12) (EIntersect e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EExpr2 e1) (EExpr2 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr2 where
  equiv (EPlusPlus e11 e12) (EPlusPlus e21 e22) env =
    equiv e11 e21 env && equiv e12 e22 env
  equiv (EExpr1 e1) (EExpr1 e2) env = equiv e1 e2 env
  equiv _ _ _ = False

instance Formula Expr1 where
  equiv (EIdent i1 e1 ea1) (EIdent i2 e2 ea2) env =
    i1 == i2 && equiv e1 e2 env && equiv ea1 ea2 env
  equiv (EExprAtom ea1) (EExprAtom ea2) env = equiv ea1 ea2 env
  equiv _ _ _ = False

instance Formula ExprAtom where
  equiv (ExprAtom eah1 eat1 _) (ExprAtom eah2 eat2 _) env =
    equiv eah1 eah2 env && equiv eat1 eat2 env

instance Formula ExprAtomHead where
  equiv (EBuiltinUnOp buo1 ea1) (EBuiltinUnOp buo2 ea2) env =
    buo1 == buo2 && equiv ea1 ea2 env
  equiv (EExpr e1) (EExpr e2) env = equiv e1 e2 env
  equiv (EIdentOrQuotedOp ioqo1) (EIdentOrQuotedOp ioqo2) env =
    equiv ioqo1 ioqo2 env
  equiv (EBoolLiteral bl1) (EBoolLiteral bl2) env = bl1 == bl2
  equiv (EIntLiteral il1) (EIntLiteral il2) env = il1 == il2
  equiv (EFloatLiteral fl1) (EFloatLiteral fl2) env = fl1 == fl2
  equiv (ESetLiteral sl1) (ESetLiteral sl2) env = equiv sl1 sl2 env
  equiv (ESetComp sc1) (ESetComp sc2) env = equiv sc1 sc2 env
  equiv (EArrayLiteral al1) (EArrayLiteral al2) env = equiv al1 al2 env
  equiv (EArrayComp ac1) (EArrayComp ac2) env = equiv ac1 ac2 env
  equiv (EIfThenElseExpr itee1) (EIfThenElseExpr itee2) env =
    equiv itee1 itee2 env
  equiv (ELetExpr le1) (ELetExpr le2) env = equiv le1 le2 env
  equiv (ECallExpr ce1) (ECallExpr ce2) env = equiv ce1 ce2 env
  equiv (EGenCallExpr gce1) (EGenCallExpr gce2) env = equiv gce1 gce2 env
  equiv _ _ _ = False

instance Formula ExprAtomTail where
  equiv EATNothing EATNothing _ = True
  equiv (ExprAtomTail aat1 eat1) (ExprAtomTail aat2 eat2) env =
    equiv aat1 aat2 env && equiv eat1 eat2 env
  equiv _ _ _ = False

instance Formula NumExpr where
  equiv (NumExpr ne1) (NumExpr ne2) = equiv ne1 ne2

instance Formula NumExpr4 where
  equiv (NPlus ne11 ne12) (NPlus ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NMinus ne11 ne12) (NMinus ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NNumExpr3 ne1) (NNumExpr3 ne2) env =
    equiv ne1 ne2 env
  equiv _ _ _ = False

instance Formula NumExpr3 where
  equiv (NStar ne11 ne12) (NStar ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NDiv ne11 ne12) (NDiv ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NMod ne11 ne12) (NMod ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NSlash ne11 ne12) (NSlash ne21 ne22) env =
    equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NNumExpr1 ne1) (NNumExpr1 ne2) env =
    equiv ne1 ne2 env
  equiv _ _ _ = False

instance Formula NumExpr1 where
  equiv (NIdent i1 ne11 ne12) (NIdent i2 ne21 ne22) env =
    equiv i1 i2 env && equiv ne11 ne21 env && equiv ne12 ne22 env
  equiv (NNumExprAtom nea1) (NNumExprAtom nea2) env =
    equiv nea1 nea2 env
  equiv _ _ _ = False

instance Formula NumExprAtom where
  equiv (NumExprAtom neah1 eat1 _) (NumExprAtom neah2 eat2 _) env =
    equiv neah1 neah2 env && equiv eat1 eat2 env

instance Formula NumExprAtomHead where
  equiv (NBuiltinNumUnOp bnuo1 nea1) (NBuiltinNumUnOp bnuo2 nea2) env =
    bnuo1 == bnuo2 && equiv nea1 nea2 env
  equiv (NNumExpr ne1) (NNumExpr ne2) env = equiv ne1 ne2 env
  equiv (NIdentOrQuotedOp ioqo1) (NIdentOrQuotedOp ioqo2) env =
    equiv ioqo1 ioqo2 env
  equiv (NIntLiteral il1) (NIntLiteral il2) env = il1 == il2
  equiv (NFloatLiteral fl1) (NFloatLiteral fl2) env = fl1 == fl2
  equiv (NIfThenElseExpr itee1) (NIfThenElseExpr itee2) env =
    equiv itee1 itee2 env
  equiv (NLetExpr le1) (NLetExpr le2) env = equiv le1 le2 env
  equiv (NCallExpr ce1) (NCallExpr ce2) env = equiv ce1 ce2 env
  equiv (NGenCallExpr gce1) (NGenCallExpr gce2) env = equiv gce1 gce2 env
  equiv _ _ _ = False

instance Formula SetLiteral where
  equiv (SetLiteral es1) (SetLiteral es2) env =
    equivLists es1 es2 env

instance Formula SetComp where
  equiv (SetComp e1 ct1) (SetComp e2 ct2) env =
    equiv e1 e2 env && equiv ct1 ct2 env

instance Formula CompTail where
  equiv (CompTail gs1 Nothing) (CompTail gs2 Nothing) env =
    equivLists gs1 gs2 env
  equiv (CompTail _ Nothing) _ _ = False
  equiv _ (CompTail _ Nothing) _ = False
  equiv (CompTail gs1 (Just e1)) (CompTail gs2 (Just e2)) env =
    equiv e1 e2 env && equivLists gs1 gs2 env

instance Formula Generator where
  equiv (Generator is1 e1) (Generator is2 e2) env =
    is1 == is2 && equiv e1 e2 env -- TODO: is is1 == is2 correct?

instance Formula ArrayLiteral where
  equiv (ArrayLiteral es1) (ArrayLiteral es2) env =
    and $ map (\(a,b) -> equiv a b env) $ zip es1 es2

instance Formula ArrayComp where
  equiv (ArrayComp e1 ct1) (ArrayComp e2 ct2) env =
    equiv e1 e2 env && equiv ct1 ct2 env

instance Formula ArrayAccessTail where
  equiv (ArrayAccessTail es1) (ArrayAccessTail es2) env =
    and $ map (\(a,b) -> equiv a b env) $ zip es1 es2

instance Formula IfThenElseExpr where
  equiv (IfThenElseExpr c1 e1 ces1 ee1) (IfThenElseExpr c2 e2 ces2 ee2) env =
    equiv c1 c2 env && equiv e1 e2 env &&
    equivTupleLists ces1 ces2 env && equiv ee1 ee2 env -- TODO equivListsTuples?

instance Formula CallExpr where
  equiv (CallExpr ioqo1 es1) (CallExpr ioqo2 es2) env =
    ioqo1 == ioqo2 && equivLists es1 es2 env

instance Formula LetExpr where
  equiv (LetExpr lis1 e1) (LetExpr lis2 e2) env =
    equiv e1 e2 env && equivLists lis1 lis2 env

instance Formula LetItem where
  equiv (LConstraintItem ci1) (LConstraintItem ci2) env =
    equiv ci1 ci2 env
  equiv (LVarDeclItem vdi1) (LVarDeclItem vdi2) env =
    equiv vdi1 vdi2 env
  equiv _ _ _ = False

instance Formula GenCallExpr where
  equiv (GenCallExpr i1 ct1 e1) (GenCallExpr i2 ct2 e2) env =
    i1 == i2 && equiv ct1 ct2 env && equiv e1 e2 env

instance Formula Ident where
  equiv i1 i2 env =
    let ident1 = fromMaybe i1 $ findOrig env i1
        ident2 = fromMaybe i2 $ findOrig env i2
    in ident1 == ident2
--    mSameType (findDecl env i1) (findDecl env i2)

instance Formula IdentOrQuotedOp where
  equiv (IIdent i1) (IIdent i2) = equiv i1 i2
