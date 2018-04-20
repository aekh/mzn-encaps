{-# LANGUAGE ConstraintKinds #-}

module Encapsulator.Common where

import CST
import FMD
import FMD.Extra

import Debug.Trace
import Data.List (sortBy)

type Heur a = a -> FMD -> [Declaration] -> Score
type Heurs a = [a] -> FMD -> [(a, Score)]

int_min :: Integer
int_min = -2147483648

int_max :: Integer
int_max = 2147483647

data Score = Score (Integer, Integer)
           | Order
           deriving (Show, Eq)

score_int :: Score
score_int = Score (int_min, int_max)

score_null :: Score
score_null = Score (0, 0)

tenquad :: Integer
tenquad = 10000000000000000

precision :: Integer
precision = tenquad

type Attitude = Score -> Integer

sort :: Attitude -> [(a, Score)] -> [((a, Score), Int)]
sort _ list@((_, Order):_) = zip list [0..]
sort att list = sortBy (comparingScore att (snd . fst))
                       $ zip list [0..]

flipscale :: Score -> Score
flipscale (Score (lb,ub)) = Score (precision - lb, precision - ub)

flipscales :: [Score] -> [Score]
flipscales = map flipscale

normalise :: [Score] -> [Score]
normalise ss = normalise' min max ss
  where max = maximum vals
        min = minimum vals
        vals = concatMap (\(Score (a,b)) -> [a,b]) ss

normalise' :: Integer -> Integer -> [Score] -> [Score]
normalise' _ _ [] = []
normalise' min max (Score (lb,ub):ss)
  | min == max = Score (precision `div` 2, precision `div` 2)
                 : normalise' min max ss
  | otherwise = Score (lb', ub') : normalise' min max ss
  where lb' = precision*(lb - min) `div` (max - min)
        ub' = precision*(ub - min) `div` (max - min)

comparingScore :: Attitude -> (a -> Score) -> a -> a -> Ordering
comparingScore a h s1 s2 =
  case (leqScore (h s1) (h s2) a, eqScore (h s1) (h s2) a) of
    (_, True) -> EQ
    (True, False) -> LT
    (False, False) -> GT

leqScore :: Score -> Score -> Attitude -> Bool
leqScore s1 s2 f = f s1 <= f s2

geqScore :: Score -> Score -> Attitude -> Bool
geqScore s1 s2 f = f s1 >= f s2

eqScore :: Score -> Score -> Attitude -> Bool
eqScore s1 s2 f = f s1 == f s2

addScore :: Score -> Score -> Score
addScore (Score (lb1, ub1)) (Score (lb2, ub2)) = Score (lb1 + lb2, ub1 + ub2)

subScore :: Score -> Score -> Score
subScore (Score (lb1, ub1)) (Score (lb2, ub2)) = Score (lb1 - lb2, ub1 - ub2)

divScore :: Score -> Score -> Score
divScore (Score (lb1, ub1)) (Score (lb2, ub2)) =
  Score (lb1 `div` lb2, ub1 `div` ub2)

mulScore :: Score -> Score -> Score
mulScore (Score (lb1, ub1)) (Score (lb2, ub2)) = Score (lb1 * lb2, ub1 * ub2)

powScore :: Score -> Score -> Score
powScore (Score (lb1, ub1)) (Score (lb2, ub2)) = Score (lb1 ^ lb2, ub1 ^ ub2)

modScore :: Score -> Score -> Score
modScore (Score (lb1, ub1)) (Score (lb2, ub2)) =
  Score (lb1 `mod` lb2, ub1 `mod` ub2)

negScore :: Score -> Score
negScore (Score (lb, ub)) = Score (-lb, -ub)

rangeScore :: Score -> Score -> Score
rangeScore (Score (lb1, ub1)) (Score (lb2, ub2)) =
  Score (f lb2 ub1, f ub2 lb1)
  where f a b
          | b > a = 0
          | otherwise = a - b + 1

subScoreNonNeg :: Score -> Score -> Score
subScoreNonNeg s1 s2 = Score (max lb 0, max ub 0)
  where Score (lb, ub) = subScore s1 s2

class IntToScore a where
  intToScore :: a -> Environment -> [Declaration] -> Score

size :: ArrayTiExprTail -> Environment -> [Declaration] -> Score
size (ArrayTiExprTail tes _) env locs =
  foldl f (Score (1,1)) tes
  where f score (TiExpr bte) =
          score `mulScore` sizeBTE bte env locs

sizeBTE :: BaseTiExpr -> Environment -> [Declaration] -> Score
sizeBTE (BaseTiExpr _ (BIdent i)) env locs =
  sizeBTE (toType i env locs) env locs
sizeBTE (BaseTiExpr _ BBool) _ _ = error "Internal error"
sizeBTE (BaseTiExpr _ BInt) _ _ = score_int
sizeBTE (BaseTiExpr _ BFloat) _ _ = error "Internal error"
sizeBTE (BaseTiExpr _ (BSetTiExprTail SInt)) _ _ = score_int
sizeBTE (BaseTiExpr _ (BSetTiExprTail (SSet es))) env locs =
  Score (lb, ub)
  where scores = map (\x -> intToScore x env locs) es
        lb = minimum $ map (\(Score (lb, _)) -> lb) scores
        ub = maximum $ map (\(Score (_, ub)) -> ub) scores
sizeBTE (BaseTiExpr _ (BSetTiExprTail (SRange ne1 ne2))) env locs =
  sizeRange ne1 ne2 env locs
sizeBTE (BaseTiExpr _ (BSetTiExprTail (SExpr6 (EUnion e1 e2)))) env locs =
  Score (min lb1 lb2, ub1 + ub2)
  where Score (lb1, ub1) = sizeBTE (toType e1 env locs) env locs
        Score (lb2, ub2) = sizeBTE (toType e2 env locs) env locs
sizeBTE (BaseTiExpr _ (BArrayTiExprTail atet@(ArrayTiExprTail _ _))) env locs =
  size atet env locs
sizeBTE (BaseTiExpr _ (BSet es)) env locs =
  Score (lb, ub)
  where scores = map (\x -> intToScore x env locs) es
        lb = minimum $ map (\(Score (lb, _)) -> lb) scores
        ub = maximum $ map (\(Score (_, ub)) -> ub) scores
sizeBTE (BaseTiExpr _ (BRange ne1 ne2)) env locs =
  sizeRange ne1 ne2 env locs
sizeBTE (BaseTiExpr _ (BExpr6 (EUnion e1 e2))) env locs =
  Score (min lb1 lb2, ub1 + ub2)
  where Score (lb1, ub1) = sizeBTE (toType e1 env locs) env locs
        Score (lb2, ub2) = sizeBTE (toType e2 env locs) env locs

sizeRange :: NumExpr -> NumExpr -> Environment -> [Declaration] -> Score
sizeRange ne1 ne2 env locs = rangeScore lower upper
  where lower = intToScore ne1 env locs
        upper = intToScore ne2 env locs

--instance IntToScore Vertex where
--  intToScore (Vertex e) = intToScore e

instance IntToScore BaseTiExpr where
  intToScore (BaseTiExpr _ btet) = intToScore btet

instance IntToScore BaseTiExprTail where
  intToScore (BIdent i) env locs = intToScore i env locs
  intToScore BInt _ _ = Score (0, int_max)
  intToScore (BSetTiExprTail stet) env locs =
    Score (0, int_max) -- TODO: make smarter?intToScore stet env locs
  intToScore (BSet es) env locs =
    Score (lb, ub)
    where scores = map (\x -> intToScore x env locs) es
          lb = minimum $ map (\(Score (x, _)) -> x) scores
          ub = maximum $ map (\(Score (_, x)) -> x) scores
  intToScore (BRange ne1 ne2) env locs =
    Score (min lb1 lb2, max ub1 ub2)
    where Score (lb1, ub1) = intToScore ne1 env locs
          Score (lb2, ub2) = intToScore ne2 env locs
  intToScore _ _ _ = error "Internal Error!"

--instance IntToScore ArrayTiExprTail where
--  intToScore atet env locs = size atet env locs

instance IntToScore Expr where
  intToScore (Expr e) = intToScore e

instance IntToScore Expr12 where
  intToScore (EEquivalence e1 e2) env locs = error "type error"
  intToScore (EExpr11 e) env locs = intToScore e env locs

instance IntToScore Expr11 where
  intToScore (ELImplies e1 e2) env locs = error "type error"
  intToScore (ERImplies e1 e2) env locs = error "type error"
  intToScore (EExpr10 e) env locs = intToScore e env locs

instance IntToScore Expr10 where
  intToScore (EOr e1 e2) env locs = error "type error"
  intToScore (EXor e1 e2) env locs = error "type error"
  intToScore (EExpr9 e) env locs = intToScore e env locs

instance IntToScore Expr9 where
  intToScore (EAnd e1 e2) env locs = error "type error"
  intToScore (EExpr8 e) env locs = intToScore e env locs

instance IntToScore Expr8 where
  intToScore (ELt e1 e2) env locs = error "type error"
  intToScore (EGt e1 e2) env locs = error "type error"
  intToScore (ELeq e1 e2) env locs = error "type error"
  intToScore (EGeq e1 e2) env locs = error "type error"
  intToScore (EEq e1 e2) env locs = error "type error"
  intToScore (EEqEq e1 e2) env locs = error "type error"
  intToScore (ENeq e1 e2) env locs = error "type error"
  intToScore (EExpr7 e) env locs = intToScore e env locs

instance IntToScore Expr7 where
  intToScore (EIn e1 e2) env locs =error "type error"
  intToScore (ESubset e1 e2) env locs =error "type error"
  intToScore (ESuperset e1 e2) env locs =error "type error"
  intToScore (EExpr6 e) env locs = intToScore e env locs

instance IntToScore Expr6 where
  intToScore (EUnion e1 e2) env locs =error "type error"
  intToScore (EDiff e1 e2) env locs =error "type error"
  intToScore (ESymDiff e1 e2) env locs =error "type error"
  intToScore (EExpr5 e) env locs = intToScore e env locs

instance IntToScore Expr5 where
  intToScore (EEllipsis e1 e2) env locs =error "type error"
  intToScore (EExpr4 e) env locs = intToScore e env locs

instance IntToScore Expr4 where
  intToScore (EPlus e1 e2) env locs =
    intToScore e1 env locs `addScore` intToScore e2 env locs
  intToScore (EMinus e1 e2) env locs =
    intToScore e1 env locs `subScore` intToScore e2 env locs
  intToScore (EExpr3 e) env locs = intToScore e env locs

instance IntToScore Expr3 where
  intToScore (EStar e1 e2) env locs =
    intToScore e1 env locs `mulScore` intToScore e2 env locs
  intToScore (EDiv e1 e2) env locs =
    intToScore e1 env locs `divScore` intToScore e2 env locs
  intToScore (EMod e1 e2) env locs =
    intToScore e1 env locs `modScore` intToScore e2 env locs
  intToScore (ESlash e1 e2) env locs =
    intToScore e1 env locs `divScore` intToScore e2 env locs
  intToScore (EIntersect e1 e2) env locs = error "type error"
  intToScore (EExpr2 e) env locs = intToScore e env locs

instance IntToScore Expr2 where
  intToScore (EPlusPlus e1 e2) env locs = error "type error"
  intToScore (EExpr1 e) env locs = intToScore e env locs

instance IntToScore Expr1 where
  intToScore (EIdent _ e ea) env locs = error "Unknown function, cannot create score."
  intToScore (EExprAtom ea) env locs = intToScore ea env locs

instance IntToScore ExprAtom where
  intToScore (ExprAtom eah _ _) env locs =
    intToScore eah env locs

instance IntToScore ExprAtomHead where
  intToScore (EBuiltinUnOp _ ea) env locs =
    negScore $ intToScore ea env locs
  intToScore (EExpr e) env locs =
    intToScore e env locs
  intToScore (EIdentOrQuotedOp ioqo) env locs =
    intToScore ioqo env locs
  intToScore (EBoolLiteral _) _ _ = error "type error"
  intToScore (EIntLiteral il) env locs = intToScore il env locs
  intToScore (EFloatLiteral _) _ _ = error "type error"
  intToScore (ESetLiteral sl) env locs = error "type error"
  intToScore (ESetComp sc) env locs = error "type error"
  intToScore (EArrayLiteral al) env locs = error "type error"
  intToScore (EArrayComp ac) env locs = error "type error"
  intToScore (EIfThenElseExpr itee) env locs =
    intToScore itee env locs
  intToScore (ELetExpr le) env locs =
    intToScore le env locs
  intToScore (ECallExpr ce) env locs =
    intToScore ce env locs
  intToScore (EGenCallExpr gce) env locs =
    intToScore gce env locs

--instance IntToScore ExprAtomTail where
--  intToScore EATNothing _ _= Number 0
--  intToScore (ExprAtomTail aat eat) env locs =
--    mixScore (intToScore aat env locs) (intToScore eat env locs)

instance IntToScore NumExpr where
  intToScore (NumExpr ne) = intToScore ne

instance IntToScore NumExpr4 where
  intToScore (NNumExpr3 ne) env locs = intToScore ne env locs
  intToScore (NPlus ne1 ne2) env locs =
    intToScore ne1 env locs `addScore` intToScore ne2 env locs
  intToScore (NMinus ne1 ne2) env locs =
    intToScore ne1 env locs `subScore` intToScore ne2 env locs

instance IntToScore NumExpr3 where
  intToScore (NNumExpr1 ne) env locs = intToScore ne env locs
  intToScore (NStar ne1 ne2) env locs =
    intToScore ne1 env locs `mulScore` intToScore ne2 env locs
  intToScore (NDiv ne1 ne2) env locs =
    intToScore ne1 env locs `divScore` intToScore ne2 env locs
  intToScore (NMod ne1 ne2) env locs =
    intToScore ne1 env locs `modScore` intToScore ne2 env locs
  intToScore (NSlash ne1 ne2) env locs =
    intToScore ne1 env locs `divScore` intToScore ne2 env locs

instance IntToScore NumExpr1 where
  intToScore (NNumExprAtom nea) env locs = intToScore nea env locs
  intToScore (NIdent i ne1 ne2) env locs = error "Unkown function, cannot create score."

instance IntToScore NumExprAtom where
  intToScore (NumExprAtom neah _ _) = intToScore neah

instance IntToScore NumExprAtomHead where
  intToScore (NBuiltinNumUnOp _ e) env locs = negScore $ intToScore e env locs
  intToScore (NNumExpr ne) env locs = intToScore ne env locs
  intToScore (NIdentOrQuotedOp ioqo) env locs = intToScore ioqo env locs
  intToScore (NIntLiteral il) env locs = intToScore il env locs
  intToScore (NFloatLiteral _) _ _ = error "type error"
  intToScore (NIfThenElseExpr itee) env locs = intToScore itee env locs
  intToScore (NLetExpr le) env locs = intToScore le env locs
  intToScore (NCallExpr ce) env locs = intToScore ce env locs
  intToScore (NGenCallExpr gce) env locs = intToScore gce env locs

instance IntToScore IntLiteral where
  intToScore (IntLiteral i) _ _ = Score (toInteger i, toInteger i)

{-instance IntToScore SetLiteral where
  intToScore (SetLiteral es) _ _ = error "type error"

instance IntToScore SetComp where
  intToScore (SetComp e ct) _ _ = error "type error"

instance IntToScore CompTail where
  intToScore (CompTail gs Nothing) env locs =
    foldl mixScore (Number 0) $ map (\x -> intToScore x env locs) gs
  intToScore (CompTail gs (Just e)) env locs =
    let scores = foldl mixScore (Number 0)
                 $ map (\x -> intToScore x env locs) gs
    in mixScore scores (intToScore e env locs)

instance IntToScore Generator where
  intToScore (Generator _ e) env locs =
    intToScore e env locs

instance IntToScore ArrayLiteral where
  intToScore (ArrayLiteral es) env locs =
    foldl mixScore (Number 0) $ map (\x -> intToScore x env locs) es

instance IntToScore ArrayComp where
  intToScore (ArrayComp e ct) env locs =
    let locs1 = ctToLocalDecls ct env locs ++ locs
    in intToScore e env locs1

instance IntToScore ArrayAccessTail where
  intToScore (ArrayAccessTail es) env locs =
    foldl mixScore (Number 0) $ map (\x -> intToScore x env locs) es
-}
instance IntToScore IfThenElseExpr where
  intToScore (IfThenElseExpr c e ces ee) env locs =
    {-maximum-} scores !! 1 -- TODO FIXME: include Attitude to pick maximum
    where scores = intToScore e env locs : intToScore ee env locs : scores1
          scores1 = map (\(a,b) -> intToScore b env locs) ces

instance IntToScore CallExpr where
  intToScore (CallExpr _ es) env locs = error "Unimplemented"

instance IntToScore LetExpr where
  intToScore (LetExpr lis e) env locs =
    let locs1 = lisToLocalDecls lis ++ locs
    in intToScore e env locs1

--instance IntToScore LetItem where
--  intToScore (LConstraintItem ci) env locs =
--    Number 0 -- intToScore ci env locs
--  intToScore (LVarDeclItem vdi) env locs =
--    Number 0 -- intToScore vdi env locs

instance IntToScore GenCallExpr where
  intToScore (GenCallExpr i ct e) env locs = error "Unimplemented"

instance IntToScore Ident where
  intToScore i env locs = case findDecl env1 i of
    Just (Declaration bte _) -> {-sizeBTE-} intToScore bte env locs
    Nothing -> error ("Error! Declaration for `" ++ show i ++ "' not found." ++
                      "\nWith Env: " ++ show env ++
                      "\n  Locals: " ++ show locs)
    where env1 = foldl (\env decl -> insertDeclaration decl env) env locs

instance IntToScore IdentOrQuotedOp where
  intToScore (IIdent i) = intToScore i

--instance IntToScore Declaration where
--  intToScore (Declaration bte _) env locs = intToScore bte env locs
