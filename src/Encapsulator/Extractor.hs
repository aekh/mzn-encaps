{-| -}
module Encapsulator.Extractor where

import Data.List (find, delete, nub, zip, transpose, sortBy)
import Data.Maybe (isJust)
import Data.Ord (comparing)

import FMD
import FMD.Extra
import CST
import CST.Utils

import Debug.Trace

--import Encapsulator.Ranker
import Encapsulator.Common

fmd :: CST -> Int -> Heurs Expr -> Attitude -> FMD
fmd cst breadth heur att =
  let exprs = constraints cst
      env = mkEnv cst
      fmd0 = emptyFMD env
      fmd1 = populateS fmd0 exprs (-1)
      -- pairs = mkPairs fmd1
      fmd2 = populateA fmd1 breadth heur att
      -- fmd3 = populateG
  in fmd2

populateS :: FMD -> [Expr] -> Int -> FMD
populateS fmd1 [] _ = fmd1
populateS fmd1 (expr : exprs) i =
  let v = Vertex expr
      (fmd2, i2, fresh) = insertVertex fmd1 v
      fmd3@(FMD env3 vs es) =
        if i >= 0
          then insertEdge fmd2 (Edge Subformula i i2)
          else fmd2
      fmd4 = if fresh
               then let (subs, env4) = subformula expr env3
                    in populateS (FMD env4 vs es) subs i2
               else fmd3
  in populateS fmd4 exprs i

populateA :: FMD -> Int -> Heurs Expr -> Attitude -> FMD
populateA (FMD env vs es) breadth heur att =
  let (abstss1, env1) = foldr h ([], env) vs
      fmd1 = FMD env1 vs es
      abstssVs = zip (map trimEnds abstss1) [0..]
  in populateA' fmd1 abstssVs breadth heur att

trimEnds :: [a] -> [a]
trimEnds (_:x:xs) = init $ x:xs
trimEnds _ = []

h :: Vertex -> ([[Expr]], Environment) -> ([[Expr]], Environment)
h (Vertex e) (abstss, env) =
  let (absts', env') = abstractions e env []
  in (nub $ absts' : abstss, env')

ezString :: Show a => [a] -> String
ezString [] = ""
ezString (x:xs) = show x ++ "\n" ++ ezString xs

populateA' :: FMD -> [([Expr], Int)] -> Int -> Heurs Expr -> Attitude -> FMD
populateA' fmd [] _ _ _ = fmd
populateA' fmd1 ((absts,parent):ts) breadth heur att =
  populateA' fmd2 ts breadth heur att
  where (candidates',_) = unzip $ take breadth f
        (candidates, _) = unzip candidates'
        fmdxs xs = extendN fmd1 xs Abstraction parent
        fmd2 = extendN fmd1 candidates Abstraction parent
        f = sort att $ heur absts $ fmdxs absts

extendN :: FMD -> [Expr] -> Relation -> Int ->  FMD
extendN fmd exprs rel parent =
  foldl f fmd exprs
  where f fmd expr = extend fmd expr rel parent

extend :: FMD -> Expr -> Relation -> Int -> FMD
extend fmd1@(FMD _ vs _) expr rel parent =
  insertEdge fmd2 (Edge rel parent i)
  where (fmd2, i, _fresh) = insertVertex fmd1 (Vertex expr)

--populateA'' :: FMD -> (Expr, Int) -> [([Expr], Int)] -> [(Int,Int)] -> FMD
--populateA'' fmd1@(FMD _ vs _) (match, i) [] _ =
--  let Vertex parent = vs !! i
--      parentScore = argumentModesty parent fmd1 []
--      score = argumentModesty match fmd1 []
--  in if score < parentScore
--       then let v = Vertex match
--                (fmd2, i1, fresh) = insertVertex fmd1 v
--                fmd3 = if fresh
--                         then insertEdge fmd2 (Edge Abstraction i i1)
--                         else insertEdge fmd2 (Edge Abstraction i i1)
--                              -- TODO: can ^ introduce multiple edges?
--            in fmd3
--       else fmd1
--populateA'' fmd@(FMD _ vs _) t@(match,i) (([],_):ts) pairs =
--  populateA'' fmd t ts pairs
--populateA'' fmd1@(FMD env _ _) t@(match,i1) ((abst:absts,i2):ts) pairs =
--  if (i1,i2) `elem` pairs
--    then if equivTypes match abst env []
--           then let v = Vertex match
--                    (fmd2, i3, fresh) = insertVertex fmd1 v
--                    fmd3 = if fresh
--                             then let fmd' = insertEdge
--                                               fmd2
--                                               (Edge Abstraction i1 i3)
--                                  in insertEdge
--                                       fmd'
--                                       (Edge Abstraction i2 i3)
--                             else fmd2
--                in populateA'' fmd3 t ((absts,i2):ts) pairs
--           else populateA'' fmd1 t ((absts,i2):ts) pairs
--    else populateA'' fmd1 t (([],i2):ts) pairs

--mkPairs :: FMD -> [(Int, Int)]
--mkPairs fmd@(FMD _ vs _) =
--  filter
--    (\(a,b) -> not (isReachable fmd a b) && canMatch fmd a b)
--    (allPairs $ length vs)

allPairs :: Int -> [(Int,Int)]
allPairs len = f 0 (len-1)
  where f :: Int -> Int -> [(Int, Int)]
        f x y
          | x > y = []
          | otherwise = zip [x] [0..y] ++ f (x+1) y

--canMatch :: FMD -> Int -> Int -> Bool
--canMatch fmd@(FMD env vs _) i1 i2 =
--  let Vertex e1 = vs !! i1
--      Vertex e2 = vs !! i2
--  in easyMatch e1 e2

isReachable :: FMD -> Int -> Int -> Bool
isReachable fmd@(FMD env vs es) i1 i2
  | i1 == i2 = True
  | otherwise =
      let f (_, xid) = isJust $ find (\(Edge _ from to) ->
                                              from == i1 && to == xid) es
          (_, is) = unzip $ filter f (zip vs [1..])
      in any (\i -> isReachable fmd i i2) is

populateG :: FMD -> FMD
populateG = undefined

strip :: Expr -> Expr
strip (Expr
       (EExpr11
        (EExpr10
         (EExpr9
          (EExpr8
           (EExpr7
            (EExpr6
             (EExpr5
              (EExpr4
               (EExpr3
                (EExpr2
                 (EExpr1
                  (EExprAtom
                   (ExprAtom (EExpr x) EATNothing (Annotations []))
                  ))))))))))))) = strip x
strip x = x

------------------------
-- SUBFORMULA FINDING --
------------------------

class Subformula a where
  subformula :: a -> Environment -> ([Expr], Environment)
  formula :: a -> Environment -> ([Expr], Environment)

instance Subformula TiExprAndId where
  subformula _ env = ([], env)
  formula (TiExprAndId te _) = formula te

instance Subformula VarDeclItem where
  subformula _ env = ([], env)
  formula (VarDeclItem teai _ Nothing) env =
    formula teai env
  formula (VarDeclItem teai _ (Just e)) env =
    let (forms1, env1) = formula teai env
        (forms2, env2) = formula e env1
    in (nub $ forms1 ++ forms2, env2)

instance Subformula ConstraintItem where
  subformula (ConstraintItem e) = subformula e
  formula (ConstraintItem e) = formula e

instance Subformula TiExpr where
  subformula _ env = ([], env)
  formula (TiExpr (BaseTiExpr _ btet)) = formula btet

instance Subformula BaseTiExprTail where
  subformula _ env = ([], env)
  formula (BIdent _) env = ([], env)
  formula BBool env = ([], env)
  formula BFloat env = ([], env)
  formula BInt env = ([], env)
  formula (BSetTiExprTail stet) env = formula stet env
  formula (BArrayTiExprTail atet) env = formula atet env
  formula (BSet es) env = foldl f ([], env) es
  formula (BRange ne1 ne2) env =
    let (forms1, env1) = formula ne1 env
        (forms2, env2) = formula ne2 env1
    in (nub $ forms1 ++ forms2, env2)
  formula (BExpr6 e) env = formula e env

instance Subformula SetTiExprTail where
  subformula _ env = ([], env)
  formula SInt env = ([], env)
  formula (SSet es) env = foldl f ([], env) es
  formula (SRange ne1 ne2) env =
    (nub $ forms1 ++ forms2, env2)
    where (forms1, env1) = formula ne1 env
          (forms2, env2) = formula ne2 env1
  formula (SExpr6 e) env = formula e env

instance Subformula ArrayTiExprTail where
  subformula _ env = ([], env)
  formula (ArrayTiExprTail tes te) env =
    (nub $ forms1 ++ forms2, env2)
    where (forms1, env1) = foldl f ([], env) tes
          (forms2, env2) = formula te env1

instance Subformula Expr where
  subformula (Expr e) = subformula e
  formula (Expr e) = formula e

instance Subformula Expr12 where
  subformula (EEquivalence e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr11 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr x]
                           ,env)
                      else subformula x env

instance Subformula Expr11 where
  subformula (ERImplies e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ELImplies e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr10 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 x]
                           ,env)
                      else subformula x env

instance Subformula Expr10 where
  subformula (EOr e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EXor e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr9 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 x]
                           ,env)
                      else subformula x env

instance Subformula Expr9 where
  subformula (EAnd e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr8 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 x]
                           ,env)
                      else subformula x env

instance Subformula Expr8 where
  subformula (ELt e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EGt e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ELeq e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EGeq e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EEqEq e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EEq e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ENeq e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr7 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 x]
                           ,env)
                      else subformula x env

instance Subformula Expr7 where
  subformula (EIn e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ESubset e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ESuperset e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr6 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 x]
                           ,env)
                      else subformula x env

instance Subformula Expr6 where
  subformula (EUnion e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EDiff e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ESymDiff e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr5 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 x]
                           ,env)
                      else subformula x env

instance Subformula Expr5 where
  subformula (EEllipsis e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr4 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 x]
                           ,env)
                      else subformula x env

instance Subformula Expr4 where
  subformula (EPlus e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EMinus e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr3 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 x]
                           ,env)
                      else subformula x env


instance Subformula Expr3 where
  subformula (EStar e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EDiv e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EMod e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (ESlash e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EIntersect e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr2 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 x]
                           ,env)
                      else subformula x env

instance Subformula Expr2 where
  subformula (EPlusPlus e1 e2) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula e2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExpr1 e) env = subformula e env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 x]
                           ,env)
                      else subformula x env

instance Subformula Expr1 where
  subformula (EIdent _i e1 ea) env =
    let (subs1, env1) = formula e1 env
        (subs2, env2) = formula ea env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (EExprAtom ea) env = subformula ea env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 x]
                           ,env)
                      else subformula x env

instance Subformula ExprAtom where
  subformula (ExprAtom eah eat _) env =
    let (subs1, env1) = subformula eah env
        (subs2, env2) = formula eat env1
    in (nub $ subs1 ++ subs2, env2)
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom x]
                           ,env)
                      else subformula x env

instance Subformula ExprAtomHead where
  subformula (EBuiltinUnOp _ ea) env = formula ea env
  subformula (EExpr e) env = subformula e env
  subformula (EIdentOrQuotedOp ioqo) env = subformula ioqo env
  subformula (EBoolLiteral _) env = ([], env) -- subformula bl env
  subformula (EIntLiteral _) env = ([], env) -- subformula il env
  subformula (EFloatLiteral _) env = ([], env) -- subformula fl env
  subformula (ESetLiteral sl) env = formula sl env
  subformula (ESetComp sc) env = formula sc env
  subformula (EArrayLiteral al) env = formula al env
  subformula (EArrayComp ac) env = formula ac env
  subformula (EIfThenElseExpr itee) env = subformula itee env
  subformula (ELetExpr le) env = subformula le env
  subformula (ECallExpr ce) env = subformula ce env
  subformula (EGenCallExpr gce) env = subformula gce env
  formula x env = if isBool x env
                      then (strip <$>
                           [Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom x EATNothing (Annotations []))]
                           ,env)
                           -- TODO: is ^this^ correct?
                      else subformula x env

instance Subformula ExprAtomTail where
  subformula _ env = ([], env)
  formula (ExprAtomTail aat eat) env =
    let (subs1, env1) = formula aat env
        (subs2, env2) = formula eat env1
    in (nub $ subs1 ++ subs2, env2)
  formula EATNothing env = ([], env)

instance Subformula NumExpr where
  subformula (NumExpr ne) = subformula ne
  formula x env = if isBool x env
                    then (strip <$> [toExpr x], env)
                    else subformula x env

instance Subformula NumExpr4 where
  subformula (NPlus ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NMinus ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NNumExpr3 ne) env = subformula ne env
  formula x env = if isBool x env
                    then (strip <$> [toExpr x], env)
                    else subformula x env

instance Subformula NumExpr3 where
  subformula (NStar ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NDiv ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NMod ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NSlash ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NNumExpr1 ne) env = subformula ne env
  formula x env = if isBool x env
                    then (strip <$> [toExpr x], env)
                    else subformula x env

instance Subformula NumExpr1 where
  subformula (NIdent _ ne1 ne2) env =
    let (subs1, env1) = formula ne1 env
        (subs2, env2) = formula ne2 env1
    in (nub $ subs1 ++ subs2, env2)
  subformula (NNumExprAtom nea) env = subformula nea env
  formula x env = if isBool x env
                      then (strip <$> [toExpr x], env)
                      else subformula x env

instance Subformula NumExprAtom where
  subformula (NumExprAtom neah eat _) env =
    let (subs1, env1) = formula neah env
        (subs2, env2) = formula eat env1
    in (nub $ subs1 ++ subs2, env2)
  formula x env = if isBool x env
                    then (strip <$> [toExpr x], env)
                    else subformula x env

instance Subformula NumExprAtomHead where
  subformula (NBuiltinNumUnOp _ nea) env = formula nea env
  subformula (NNumExpr ne) env = subformula ne env
  subformula (NIdentOrQuotedOp ioqo) env = subformula ioqo env
  subformula (NIntLiteral _) env = ([], env)
  subformula (NFloatLiteral _) env = ([], env)
  subformula (NIfThenElseExpr itee) env = subformula itee env
  subformula (NLetExpr le) env = subformula le env
  subformula (NCallExpr ce) env = subformula ce env
  subformula (NGenCallExpr gce) env = subformula gce env
  formula x env = if isBool x env
                    then (strip <$> [toExpr x], env)
                    else subformula x env

instance Subformula SetLiteral where
  subformula _ env = ([], env) -- TODO: correct?
  formula (SetLiteral es) env =
    foldl f ([], env) es

instance Subformula SetComp where
  subformula _ env = ([], env) -- TODO: correct?
  formula (SetComp e ct) env =
    let (subs1, env1) = formula e env
        (subs2, env2) = formula ct env1
        subformulas = nub $ subs1 ++ subs2
    in freshify subformulas ct env2

instance Subformula CompTail where
  subformula _ env = ([], env)
  formula (CompTail gs Nothing) env =
    foldl f ([], env) gs
  formula (CompTail gs (Just e)) env =
    foldl f (formula e env) gs

instance Subformula Generator where
  subformula _ env = ([], env)
  formula (Generator _ e) = formula e

instance Subformula ArrayLiteral where
  subformula _ env = ([], env)
  formula (ArrayLiteral es) env =
    foldl f ([], env) es

instance Subformula ArrayComp where
  subformula _ env = ([], env)
  formula (ArrayComp e ct) env =
    let (subs1, env1) = formula e env
        (subs2, env2) = formula ct env1
        subformulas = nub $ subs1 ++ subs2
    in freshify subformulas ct env2

instance Subformula ArrayAccessTail where
  subformula _ env = ([], env) -- TODO: correct?
  formula (ArrayAccessTail es) env =
    foldl f ([], env) es

instance Subformula IfThenElseExpr where
  subformula (IfThenElseExpr c e ces ee) env =
    let (subs1, env1) = formula c env
        (subs2, env2) = formula e env1
        (subs3, env3) = foldl
                        (\(es, env) (c,e) ->
                           let (subs1, env1) = formula c env
                               (subs2, env2) = formula e env2
                           in (nub $ subs1 ++ subs2, env2))
                        ([], env2)
                        ces
        (subs4, env4) = formula ee env3
    in (nub $ subs1 ++ subs2 ++ subs3 ++ subs4, env4)
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (EIfThenElseExpr x)
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else subformula x env

instance Subformula CallExpr where
  subformula (CallExpr _ es) env =
    foldl f ([], env) es
  formula (CallExpr (IIdent (Ident "bool2int")) [e]) env =
    formula e env
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (ECallExpr x)
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else subformula x env

f :: Subformula a => ([Expr], Environment) -> a -> ([Expr], Environment)
f (es, env) li = let (es', env') = formula li env
                 in (nub $ es ++ es', env')

instance Subformula LetExpr where
  subformula le@(LetExpr lis e) env =
    let (subs1, env1) = foldl f ([],env) lis
        (subs2, env2) = formula e env1
        subformulas = nub $ subs1 ++ subs2
    in freshify subformulas le env2
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (ELetExpr x)
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else subformula x env

instance Subformula LetItem where
  subformula _ env = ([], env)
  formula (LConstraintItem ci) env = formula ci env
  formula (LVarDeclItem vdi) env = formula vdi env

instance Subformula GenCallExpr where
  subformula (GenCallExpr _ ct e) env =
    let (subs1, env1) = formula e env
        (subs2, env2) = formula ct env1
        subformulas = nub $ subs1 ++ subs2
    in freshify subformulas ct env2
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (EGenCallExpr x)
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else subformula x env

instance Subformula Ident where
  subformula _ env = ([], env)
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (EIdentOrQuotedOp (IIdent x))
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else ([], env)

instance Subformula IdentOrQuotedOp where
  subformula _ env = ([], env)
  formula x env = if isBool x env
                      then ([Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                            EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
                            EExpr2 $ EExpr1 $ EExprAtom
                            (ExprAtom
                              (EIdentOrQuotedOp x)
                              EATNothing
                              (Annotations []))]
                           ,env)
                      else ([], env)

----------------------------
-- GENERALISATION FINDING --
----------------------------

class Generalisation a where;

-------------------------
-- ABSTRACTION FINDING --
-------------------------

combineM :: (a -> b -> c) -> [a] -> [b] -> [c]
combineM _ _ [] = []
combineM _ [] _ = []
combineM m [a] (b:bs) = m a b : combineM m [a] bs
combineM m (a:as) [b] = m a b : combineM m as [b]
combineM m (a:as) bs = combineM m [a] bs ++ combineM m as bs

mkAbstraction :: (Show a, ToExpr a, Abstraction a, Types a) =>
                 a -> Environment -> [Declaration] -> (Environment, Ident)
mkAbstraction x env locs = --(env, Ident "TEST")
  case findAbstr env (toExpr x) of
    Nothing -> (insertAbstr (Abstr (toExpr x) iNew) env1, iNew)
    Just iOld -> (insertAbstr (Abstr (toExpr x) iOld) env, iOld)
  where bte =  toType x env locs
        decl = Declaration bte (Ident "ADUMMY")
        (env1, iNew) = freshDecl env decl

class Abstraction a where
  abstractions :: a -> Environment -> [Declaration] -> ([a], Environment)

instance Abstraction ConstraintItem where
  abstractions (ConstraintItem e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (ConstraintItem <$>  absts1, env1)

instance Abstraction Expr where
  abstractions (Expr e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (Expr <$>  absts1, env1)

instance Abstraction Expr12 where
  abstractions (EEquivalence e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EEquivalence absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr11 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr11 <$>  absts1, env1)

instance Abstraction Expr11 where
  abstractions (ERImplies e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ERImplies absts1 absts2
    in (nub absts, env2)
  abstractions (ELImplies e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ELImplies absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr10 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr10 <$>  absts1, env1)

instance Abstraction Expr10 where
  abstractions (EOr e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EOr absts1 absts2
    in (nub absts, env2)
  abstractions (EXor e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EXor absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr9 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr9 <$>  absts1, env1)

instance Abstraction Expr9 where
  abstractions (EAnd e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EAnd absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr8 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr8 <$>  absts1, env1)

instance Abstraction Expr8 where
  abstractions (ELt e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ELt absts1 absts2
    in (nub absts, env2)
  abstractions (EGt e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EGt absts1 absts2
    in (nub absts, env2)
  abstractions (ELeq e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ELeq absts1 absts2
    in (nub absts, env2)
  abstractions (EGeq e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EGeq absts1 absts2
    in (nub absts, env2)
  abstractions (EEqEq e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EEqEq absts1 absts2
    in (nub absts, env2)
  abstractions (EEq e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EEq absts1 absts2
    in (nub absts, env2)
  abstractions (ENeq e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ENeq absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr7 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr7 <$>  absts1, env1)

instance Abstraction Expr7 where
  abstractions (EIn e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EIn absts1 absts2
    in (nub absts, env2)
  abstractions (ESubset e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ESubset absts1 absts2
    in (nub absts, env2)
  abstractions (ESuperset e1 e2) env locs =
    let (absts1, env1) = abstractions e1 env locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ESuperset absts1 absts2
    in (nub absts, env2)
  abstractions (EExpr6 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr6 <$>  absts1, env1)

instance Abstraction Expr6 where
  abstractions ee@(EUnion e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EUnion absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(EDiff e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EDiff absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(ESymDiff e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ESymDiff absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExpr5 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr5 <$>  absts1, env1)

instance Abstraction Expr5 where
  abstractions ee@(EEllipsis e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        --(absts1, env1) = abstractions e1 env' locs
        (_absts2, env2) = ([], env') -- abstractions e2 env1 locs
        absts = [] -- combineM EEllipsis absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExpr4 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr4 <$>  absts1, env1)

instance Abstraction Expr4 where
  abstractions ee@(EPlus e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EPlus absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(EMinus e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr3 $ EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EMinus absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExpr3 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr3 <$>  absts1, env1)

instance Abstraction Expr3 where
  abstractions ee@(EStar e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EStar absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(EDiv e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EDiv absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(EMod e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EMod absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(ESlash e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM ESlash absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions ee@(EIntersect e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr2 $ EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EIntersect absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExpr2 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr2 <$>  absts1, env1)

instance Abstraction Expr2 where
  abstractions ee@(EPlusPlus e1 e2) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExpr1 $
               EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions e2 env1 locs
        absts = combineM EPlusPlus absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExpr1 e) env locs =
    let (absts1, env1) = abstractions e env locs
    in (EExpr1 <$>  absts1, env1)

instance Abstraction Expr1 where
  abstractions ee@(EIdent i e1 ea) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EExprAtom (ExprAtom
                           (EIdentOrQuotedOp (IIdent i'))
                           EATNothing
                           (Annotations []))
        (absts1, env1) = abstractions e1 env' locs
        (absts2, env2) = abstractions ea env1 locs
        absts = combineM (EIdent i) absts1 absts2
    in if hasLocal ee env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)
  abstractions (EExprAtom ea) env locs =
    let (absts1, env1) = abstractions ea env locs
    in (EExprAtom <$>  absts1, env1)

instance Abstraction ExprAtom where
  abstractions (ExprAtom eah EATNothing as) env locs =
    let (absts1, env1) = abstractions eah env locs
    in ((\x -> ExprAtom x EATNothing as) <$>  absts1, env1)
  abstractions ea@(ExprAtom eah eat as) env locs =
    let (env', i') = mkAbstraction ea env locs
        abst = ExprAtom
                 (EIdentOrQuotedOp (IIdent i'))
                 EATNothing
                 (Annotations [])
        (absts1, env1) = abstractions eah env' locs
        (absts2, env2) = abstractions eat env1 locs
        absts = combineM (\x y -> ExprAtom x y as) absts1 absts2
    in if hasLocal ea env locs
         then (nub absts, env2)
         else (nub $ abst : absts, env2)

instance Abstraction ExprAtomHead where
  abstractions (EBuiltinUnOp BNot ea) env locs =
    let (absts0, env1) = abstractions ea env locs
        absts = (BNot `EBuiltinUnOp`) <$> absts0
    in (nub absts, env1)
  abstractions ee@(EBuiltinUnOp buo ea) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions ea env' locs
        absts = (buo `EBuiltinUnOp`) <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(EExpr e) env locs = -- TODO: P(x,(y+1)) can't abstract (y+1)
                                       --       only y+1
    let --(env', i') = mkAbstraction ee env locs
        --abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions e env locs
        absts = EExpr <$> absts0
    in (nub absts, env1)
  abstractions ee@(EIdentOrQuotedOp _) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        absts = [ee]
    in if hasLocal ee env locs
         then (nub absts, env')
         else (nub $ abst : absts, env')
  abstractions ee@(EBoolLiteral _) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        absts = [ee]
    in if hasLocal ee env locs
         then (nub absts, env')
         else (nub $ abst : absts, env')
  abstractions ee@(EIntLiteral _) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        absts = [ee]
    in (nub $ abst : absts, env')
  abstractions ee@(EFloatLiteral _) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        absts = [ee]
    in (nub $ abst : absts, env')
  abstractions ee@(ESetLiteral sl) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = ([], env') -- abstractions sl env' locs
        absts = ESetLiteral <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(ESetComp sc) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions sc env' locs
        absts = ESetComp <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(EArrayLiteral al) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = ([], env') -- abstractions al env' locs
        absts = EArrayLiteral <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(EArrayComp ac) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions ac env' locs
        absts = EArrayComp <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(EIfThenElseExpr itee) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions itee env' locs
        absts = EIfThenElseExpr <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(ELetExpr le) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions le env' locs
        absts = ELetExpr <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(ECallExpr ce) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions ce env' locs
        absts = ECallExpr <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)
  abstractions ee@(EGenCallExpr gce) env locs =
    let (env', i') = mkAbstraction ee env locs
        abst = EIdentOrQuotedOp (IIdent i')
        (absts0, env1) = abstractions gce env' locs
        absts = EGenCallExpr <$> absts0
    in if hasLocal ee env locs
         then (nub absts, env1)
         else (nub $ abst : absts, env1)

instance Abstraction ExprAtomTail where
  abstractions EATNothing env _ = ([EATNothing], env)
  abstractions (ExprAtomTail aat eat) env locs =
    let (absts1, env1) = abstractions aat env locs
        (absts2, env2) = abstractions eat env1 locs
        absts = combineM ExprAtomTail absts1 absts2
    in (nub absts, env2)

instance Abstraction SetLiteral where
  abstractions (SetLiteral es) env locs =
    let (absts1, env1) = foldl f ([], env) es
        absts = SetLiteral <$> combineL absts1
    in (nub absts, env1)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')

instance Abstraction SetComp where
  abstractions (SetComp e ct) env locs =
    let locs' = ctToLocalDecls ct env locs ++ locs
        (absts1, env1) = abstractions e env locs'
        (absts2, env2) = abstractions ct env1 locs'
        absts1' = combineM SetComp absts1 [ct]
        absts2' = combineM SetComp [e] absts2
        absts = absts1' ++ absts2'
    in (nub absts, env2)

combineL :: [[a]] -> [[a]]
combineL [] = []
combineL (x:xs) = foldl (flip introduce) (transpose [x]) xs

introduce :: [a] -> [[a]] -> [[a]]
introduce [] _ = []
introduce _ [] = []
introduce (x:xs) (ys:yss) =
  (x:ys) : introduce xs [ys] ++ introduce (x:xs) yss

instance Abstraction CompTail where
  abstractions (CompTail gs Nothing) env locs =
    let (absts1, env1) = foldl f ([], env) gs
        absts = combineM CompTail (combineL absts1) [Nothing]
    in (nub absts, env1)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')
  abstractions (CompTail gs (Just e)) env locs =
    let (absts1, env1) = foldl f ([], env) gs
        (absts2, env2) = abstractions e env1 locs
        absts = combineM CompTail (combineL absts1) (Just <$> absts2)
    in (nub absts, env2)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')

instance Abstraction Generator where
  abstractions (Generator is e) env locs =
    let (absts1, env1) = abstractions e env locs
        absts = combineM Generator [is] absts1
    in (nub absts, env1)

instance Abstraction ArrayLiteral where
  abstractions (ArrayLiteral es) env locs =
    let (absts1, env1) = foldl f ([], env) es
        absts = ArrayLiteral <$> combineL absts1
    in (nub absts, env1)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')

instance Abstraction ArrayComp where
  abstractions (ArrayComp e ct) env locs =
    let locs' = ctToLocalDecls ct env locs ++ locs
        (absts1, env1) = abstractions e env locs'
        (absts2, env2) = abstractions ct env1 locs'
        absts = combineM ArrayComp absts1 absts2
    in (nub absts, env2)

instance Abstraction ArrayAccessTail where
  abstractions (ArrayAccessTail es) env locs =
    let (absts1, env1) = foldl f ([], env) es
        absts = ArrayAccessTail <$> combineL absts1
    in (nub absts, env1)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')

combineItee :: (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
combineItee _ _ _ _ [] = []
combineItee _ _ _ [] _ = []
combineItee _ _ [] _ _ = []
combineItee _ [] _ _ _ = []
combineItee m (a:as) (b:bs) (c:cs) (d:ds) =
  m a b c d : combineItee m as (b:bs) (c:cs) (d:ds) ++
              combineItee m (a:as) bs (c:cs) (d:ds) ++
              combineItee m (a:as) (b:bs) cs (d:ds) ++
              combineItee m (a:as) (b:bs) (c:cs) ds

instance Abstraction IfThenElseExpr where
  abstractions (IfThenElseExpr c e ces ee) env locs =
    let (absts1, env1) = abstractions c env locs
        (absts2, env2) = abstractions e env1 locs
        (absts3, env3) = foldl f ([], env2) ces
        (absts4, env4) = abstractions ee env3 locs
        absts = combineItee IfThenElseExpr absts1 absts2 (combineL absts3) absts4
    in (nub absts, env4)
    where f (abstss, env) (c,e) =
            let (absts1, env1) = abstractions c env locs
                (absts2, env2) = abstractions e env1 locs
                absts = combineM (,) absts1 absts2
            in (nub $ absts : abstss, env2)

instance Abstraction CallExpr where
  abstractions (CallExpr i es) env locs =
    let (absts1, env1) = foldl f ([], env) es
        absts = CallExpr i <$> combineL absts1
    in (nub absts, env1)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs
            in (nub $ absts' : abstss, env')

instance Abstraction LetExpr where
  abstractions (LetExpr lis e) env locs =
    let (absts1, env1) = foldl f ([], env) lis
        locs1 = lisToLocalDecls lis ++ locs
        (absts2, env2) = abstractions e env1 locs1
        absts = combineM LetExpr (combineL absts1) absts2
    in (nub absts, env2)
    where f (abstss, env) e =
            let (absts', env') = abstractions e env locs -- TODO: locs1?
            in (nub $ absts' : abstss, env')

instance Abstraction LetItem where
--  abstractions (LConstraintItem ci) env locs = undefined
  abstractions li env _ = ([li], env)

instance Abstraction GenCallExpr where
  abstractions (GenCallExpr i ct e) env locs =
    let locs' = ctToLocalDecls ct env locs ++ locs
        (absts1, env1) = abstractions ct env locs'
        (absts2, env2) = abstractions e env1 locs'
        absts = combineM (GenCallExpr i) absts1 absts2
    in (nub absts, env2)

instance Abstraction Ident where
  abstractions i env _ = ([i], env)

instance Abstraction IdentOrQuotedOp where
  abstractions (IIdent i) env locs =
    let (absts1, env1) = abstractions i env locs
    in (IIdent <$> absts1, env1)

-----------------------------------------
-- EQUIV TYPES FOR ABSTRACTION FINDING --
-----------------------------------------

equivTypesLists :: (Eq a, FormulaA a) =>
                   [a] -> [a] -> Environment -> [Declaration] -> Bool
equivTypesLists [] [] _ _ = True
equivTypesLists [] _ _ _ = False
equivTypesLists _ [] _ _ = False
equivTypesLists (x:xs) ys env locs =
  case find (\a -> equivTypes x a env locs) ys of
    Just match -> equivTypesLists xs (delete match ys) env locs
    Nothing -> False

equivTypesTupleLists :: (Eq a, Eq b, FormulaA a, FormulaA b) =>
                   [(a,b)] -> [(a,b)] -> Environment -> [Declaration] -> Bool
equivTypesTupleLists [] [] _ _ = True
equivTypesTupleLists [] _ _ _ = False
equivTypesTupleLists _ [] _ _ = False
equivTypesTupleLists ((x1,x2):xs) ys env locs =
  case find (\(a,b) -> equivTypes x1 a env locs && equivTypes x2 b env locs) ys of
    Just match -> equivTypesTupleLists xs (delete match ys) env locs
    Nothing -> False

class FormulaA a where
  equivTypes :: a -> a -> Environment -> [Declaration] -> Bool

instance FormulaA Vertex where
  equivTypes (Vertex e1) (Vertex e2) = equivTypes e1 e2

instance FormulaA TiExprAndId where
  equivTypes (TiExprAndId (TiExpr (BaseTiExpr _ btet1)) _)
        (TiExprAndId (TiExpr (BaseTiExpr _ btet2)) _) =
    equivTypes btet1 btet2

instance FormulaA VarDeclItem where
  equivTypes (VarDeclItem teai1 i1 Nothing) (VarDeclItem teai2 i2 Nothing) env locs =
    i1 == i2 && equivTypes teai1 teai2 env locs
  equivTypes (VarDeclItem teai1 i1 (Just e1)) (VarDeclItem teai2 i2 (Just e2)) env locs =
    i1 == i2 && equivTypes teai1 teai2 env locs && equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA ConstraintItem where
  equivTypes (ConstraintItem e1) (ConstraintItem e2) = equivTypes e1 e2

instance FormulaA BaseTiExprTail where
  equivTypes (BIdent i1) (BIdent i2) env locs = equivTypes i1 i2 env locs
  equivTypes BBool BBool _ _ = True
  equivTypes BFloat BFloat _ _ = True
  equivTypes BInt BInt _ _ = True
  --formula (BSetTiExprTail stet) env locs = undefined
    -- BSetTiExprTail$ substitutePart stet env locs
  --formula (BArrayTiExprTail atet) env locs = undefined
    -- BArrayTiExprTail $ substitutePart atet env locs
  equivTypes (BSet es1) (BSet es2) env locs = equivTypesLists es1 es2 env locs
  equivTypes (BRange ne11 ne12) (BRange ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (BExpr6 e1) (BExpr6 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr where
  equivTypes (Expr e1) (Expr e2) = equivTypes e1 e2

instance FormulaA Expr12 where
  equivTypes (EEquivalence e11 e12) (EEquivalence e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr11 e22) env locs && equivTypes (EExpr11 e12) e21 env locs)
  equivTypes (EExpr11 e1) (EExpr11 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr11 where
  equivTypes (ELImplies e11 e12) (ELImplies e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ERImplies e11 e12) (ERImplies e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ELImplies e11 e12) (ERImplies e21 e22) env locs =
    equivTypes e11 (EExpr10 e22) env locs && equivTypes (EExpr10 e12) e21 env locs
  equivTypes (ERImplies e11 e12) (ELImplies e21 e22) env locs =
    equivTypes e11 (EExpr10 e22) env locs && equivTypes (EExpr10 e12) e21 env locs
  equivTypes (EExpr10 e1) (EExpr10 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr10 where
  equivTypes (EOr e11 e12) (EOr e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr9 e22) env locs && equivTypes (EExpr9 e12) e21 env locs)
  equivTypes (EXor e11 e12) (EXor e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr9 e22) env locs && equivTypes (EExpr9 e12) e21 env locs)
  equivTypes (EExpr9 e1) (EExpr9 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr9 where
  equivTypes (EAnd e11 e12) (EAnd e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr8 e22) env locs && equivTypes (EExpr8 e12) e21 env locs)
  equivTypes (EExpr8 e1) (EExpr8 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr8 where
  equivTypes (EGt e11 e12) e env locs =
    equivTypes (ELt e12 e11) e env locs
  equivTypes e (EGt e11 e12) env locs =
    equivTypes e (ELt e12 e11) env locs
  equivTypes (EGeq e11 e12) e env locs =
    equivTypes (ELeq e12 e11) e env locs
  equivTypes e (EGeq e11 e12) env locs =
    equivTypes e (ELeq e12 e11) env locs
  equivTypes (EEqEq e11 e12) e env locs =
    equivTypes (EEq e12 e11) e env locs
  equivTypes e (EEqEq e11 e12) env locs =
    equivTypes e (EEq e12 e11) env locs

  equivTypes (ELt e11 e12) (ELt e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ELeq e11 e12) (ELeq e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EEq e11 e12) (EEq e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 e22 env locs && equivTypes e12 e21 env locs)
  equivTypes (ENeq e11 e12) (ENeq e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 e22 env locs && equivTypes e12 e21 env locs)
  equivTypes (EExpr7 e1) (EExpr7 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr7 where
  equivTypes (EIn e11 e12) (EIn e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ESubset e11 e12) (ESubset e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ESuperset e11 e12) (ESuperset e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EExpr6 e1) (EExpr6 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr6 where
  equivTypes (EUnion e11 e12) (EUnion e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr5 e22) env locs && equivTypes (EExpr5 e12) e21 env locs)
  equivTypes (EDiff e11 e12) (EDiff e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ESymDiff e11 e12) (ESymDiff e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr5 e22) env locs && equivTypes (EExpr5 e12) e21 env locs)
  equivTypes (EExpr5 e1) (EExpr5 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr5 where
  equivTypes (EEllipsis e11 e12) (EEllipsis e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EExpr4 e1) (EExpr4 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr4 where
  equivTypes (EPlus e11 e12) (EPlus e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr3 e22) env locs && equivTypes (EExpr3 e12) e21 env locs)
  equivTypes (EMinus e11 e12) (EMinus e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr3 e22) env locs && equivTypes (EExpr3 e12) e21 env locs)
  equivTypes (EExpr3 e1) (EExpr3 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr3 where
  equivTypes (EStar e11 e12) (EStar e21 e22) env locs =
    (equivTypes e11 e21 env locs && equivTypes e12 e22 env locs) ||
    (equivTypes e11 (EExpr2 e22) env locs && equivTypes (EExpr2 e12) e21 env locs)
  equivTypes (EDiv e11 e12) (EDiv e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EMod e11 e12) (EMod e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (ESlash e11 e12) (ESlash e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EIntersect e11 e12) (EIntersect e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EExpr2 e1) (EExpr2 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr2 where
  equivTypes (EPlusPlus e11 e12) (EPlusPlus e21 e22) env locs =
    equivTypes e11 e21 env locs && equivTypes e12 e22 env locs
  equivTypes (EExpr1 e1) (EExpr1 e2) env locs = equivTypes e1 e2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA Expr1 where
  equivTypes (EIdent i1 e1 ea1) (EIdent i2 e2 ea2) env locs =
    i1 == i2 && equivTypes e1 e2 env locs && equivTypes ea1 ea2 env locs
  equivTypes (EExprAtom ea1) (EExprAtom ea2) env locs = equivTypes ea1 ea2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA ExprAtom where
  equivTypes (ExprAtom eah1 eat1 _) (ExprAtom eah2 eat2 _) env locs =
    equivTypes eah1 eah2 env locs && equivTypes eat1 eat2 env locs

instance FormulaA ExprAtomHead where
  equivTypes (EBuiltinUnOp buo1 ea1) (EBuiltinUnOp buo2 ea2) env locs =
    buo1 == buo2 && equivTypes ea1 ea2 env locs
  equivTypes (EExpr e1) (EExpr e2) env locs = equivTypes e1 e2 env locs
  equivTypes (EIdentOrQuotedOp ioqo1) (EIdentOrQuotedOp ioqo2) env locs =
    equivTypes ioqo1 ioqo2 env locs
  equivTypes (EBoolLiteral bl1) (EBoolLiteral bl2) env locs = bl1 == bl2
  equivTypes (EIntLiteral il1) (EIntLiteral il2) env locs = il1 == il2
  equivTypes (EFloatLiteral fl1) (EFloatLiteral fl2) env locs = fl1 == fl2
  equivTypes (ESetLiteral sl1) (ESetLiteral sl2) env locs = equivTypes sl1 sl2 env locs
  equivTypes (ESetComp sc1) (ESetComp sc2) env locs = equivTypes sc1 sc2 env locs
  equivTypes (EArrayLiteral al1) (EArrayLiteral al2) env locs = equivTypes al1 al2 env locs
  equivTypes (EArrayComp ac1) (EArrayComp ac2) env locs = equivTypes ac1 ac2 env locs
  equivTypes (EIfThenElseExpr itee1) (EIfThenElseExpr itee2) env locs =
    equivTypes itee1 itee2 env locs
  equivTypes (ELetExpr le1) (ELetExpr le2) env locs = equivTypes le1 le2 env locs
  equivTypes (ECallExpr ce1) (ECallExpr ce2) env locs = equivTypes ce1 ce2 env locs
  equivTypes (EGenCallExpr gce1) (EGenCallExpr gce2) env locs = equivTypes gce1 gce2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA ExprAtomTail where
  equivTypes EATNothing EATNothing _ _ = True
  equivTypes (ExprAtomTail aat1 eat1) (ExprAtomTail aat2 eat2) env locs =
    equivTypes aat1 aat2 env locs && equivTypes eat1 eat2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA NumExpr where
  equivTypes (NumExpr ne1) (NumExpr ne2) = equivTypes ne1 ne2

instance FormulaA NumExpr4 where
  equivTypes (NPlus ne11 ne12) (NPlus ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NMinus ne11 ne12) (NMinus ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NNumExpr3 ne1) (NNumExpr3 ne2) env locs =
    equivTypes ne1 ne2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA NumExpr3 where
  equivTypes (NStar ne11 ne12) (NStar ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NDiv ne11 ne12) (NDiv ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NMod ne11 ne12) (NMod ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NSlash ne11 ne12) (NSlash ne21 ne22) env locs =
    equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NNumExpr1 ne1) (NNumExpr1 ne2) env locs =
    equivTypes ne1 ne2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA NumExpr1 where
  equivTypes (NIdent i1 ne11 ne12) (NIdent i2 ne21 ne22) env locs =
    equivTypes i1 i2 env locs && equivTypes ne11 ne21 env locs && equivTypes ne12 ne22 env locs
  equivTypes (NNumExprAtom nea1) (NNumExprAtom nea2) env locs =
    equivTypes nea1 nea2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA NumExprAtom where
  equivTypes (NumExprAtom neah1 eat1 _) (NumExprAtom neah2 eat2 _) env locs =
    equivTypes neah1 neah2 env locs && equivTypes eat1 eat2 env locs

instance FormulaA NumExprAtomHead where
  equivTypes (NBuiltinNumUnOp bnuo1 nea1) (NBuiltinNumUnOp bnuo2 nea2) env locs =
    bnuo1 == bnuo2 && equivTypes nea1 nea2 env locs
  equivTypes (NNumExpr ne1) (NNumExpr ne2) env locs = equivTypes ne1 ne2 env locs
  equivTypes (NIdentOrQuotedOp ioqo1) (NIdentOrQuotedOp ioqo2) env locs =
    equivTypes ioqo1 ioqo2 env locs
  equivTypes (NIntLiteral il1) (NIntLiteral il2) env locs = il1 == il2
  equivTypes (NFloatLiteral fl1) (NFloatLiteral fl2) env locs = fl1 == fl2
  equivTypes (NIfThenElseExpr itee1) (NIfThenElseExpr itee2) env locs =
    equivTypes itee1 itee2 env locs
  equivTypes (NLetExpr le1) (NLetExpr le2) env locs = equivTypes le1 le2 env locs
  equivTypes (NCallExpr ce1) (NCallExpr ce2) env locs = equivTypes ce1 ce2 env locs
  equivTypes (NGenCallExpr gce1) (NGenCallExpr gce2) env locs = equivTypes gce1 gce2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA SetLiteral where
  equivTypes (SetLiteral es1) (SetLiteral es2) = equivTypesLists es1 es2

instance FormulaA SetComp where
  equivTypes (SetComp e1 ct1) (SetComp e2 ct2) env locs =
    let locs1 = ctToLocalDecls ct1 env locs ++ locs
        locs2 = ctToLocalDecls ct2 env locs ++ locs1
    in equivTypes e1 e2 env locs2 && equivTypes ct1 ct2 env locs2

instance FormulaA CompTail where
  equivTypes (CompTail gs1 Nothing) (CompTail gs2 Nothing) env locs =
    equivTypesLists gs1 gs2 env locs
  equivTypes (CompTail _ Nothing) _ _ _ = False
  equivTypes _ (CompTail _ Nothing) _ _ = False
  equivTypes (CompTail gs1 (Just e1)) (CompTail gs2 (Just e2)) env locs =
    equivTypes e1 e2 env locs && equivTypesLists gs1 gs2 env locs

instance FormulaA Generator where
  equivTypes (Generator is1 e1) (Generator is2 e2) env locs =
    is1 == is2 && equivTypes e1 e2 env locs -- TODO: is is1 == is2 correct?

instance FormulaA ArrayLiteral where
  equivTypes (ArrayLiteral es1) (ArrayLiteral es2) env locs =
    all (\(a,b) -> equivTypes a b env locs) $ zip es1 es2

instance FormulaA ArrayComp where
  equivTypes (ArrayComp e1 ct1) (ArrayComp e2 ct2) env locs =
    let locs1 = ctToLocalDecls ct1 env locs ++ locs
        locs2 = ctToLocalDecls ct2 env locs ++ locs1
    in equivTypes e1 e2 env locs2 && equivTypes ct1 ct2 env locs2

instance FormulaA ArrayAccessTail where
  equivTypes (ArrayAccessTail es1) (ArrayAccessTail es2) env locs =
    all (\(a,b) -> equivTypes a b env locs) $ zip es1 es2

instance FormulaA IfThenElseExpr where
  equivTypes (IfThenElseExpr c1 e1 ces1 ee1) (IfThenElseExpr c2 e2 ces2 ee2) env locs =
    equivTypes c1 c2 env locs && equivTypes e1 e2 env locs &&
    equivTypesTupleLists ces1 ces2 env locs && equivTypes ee1 ee2 env locs -- TODO equivTypesListsTuples?

instance FormulaA CallExpr where
  equivTypes (CallExpr ioqo1 es1) (CallExpr ioqo2 es2) env locs =
    ioqo1 == ioqo2 && equivTypesLists es1 es2 env locs

instance FormulaA LetExpr where
  equivTypes (LetExpr lis1 e1) (LetExpr lis2 e2) env locs =
    let locs1 = lisToLocalDecls lis1 ++ locs
        locs2 = lisToLocalDecls lis2 ++ locs1
    in equivTypes e1 e2 env locs2 && equivTypesLists lis1 lis2 env locs2

instance FormulaA LetItem where
  equivTypes (LConstraintItem ci1) (LConstraintItem ci2) env locs =
    equivTypes ci1 ci2 env locs
  equivTypes (LVarDeclItem vdi1) (LVarDeclItem vdi2) env locs =
    equivTypes vdi1 vdi2 env locs
  equivTypes _ _ _ _ = False

instance FormulaA GenCallExpr where
  equivTypes (GenCallExpr i1 ct1 e1) (GenCallExpr i2 ct2 e2) env locs =
    let locs1 = ctToLocalDecls ct1 env locs ++ locs
        locs2 = ctToLocalDecls ct2 env locs ++ locs1
    in i1 == i2 && equivTypes ct1 ct2 env locs2 && equivTypes e1 e2 env locs2

instance FormulaA Ident where
  equivTypes i1 i2 env locs =
    let bte1 = case findDecl env1 i1 of
                 Just (Declaration bte _) -> bte
                 Nothing -> error
                            ("Error! Declaration for `" ++ show i1 ++
                             "' not found equivTypes." ++
                             "\nWith Env Locs: " ++ show env)
        bte2 = case findDecl env1 i2 of
                 Just (Declaration bte _) -> bte
                 Nothing -> error
                            ("Error! Declaration for `" ++ show i2 ++
                             "' not found in equivTypes." ++
                             "\nWith Env: " ++ show env)
    in {-trace ("bte1: " ++ show bte1 ++ ", bte2: " ++ show bte2)-} bte1 == bte2
    where env1 = foldl (flip insertDeclaration) env locs
--    mSameType (findDecl env i1) (findDecl env i2)

instance FormulaA IdentOrQuotedOp where
  equivTypes (IIdent i1) (IIdent i2) = equivTypes i1 i2
