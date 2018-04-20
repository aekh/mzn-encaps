module Encapsulator.Ranker where

import qualified Data.List as L
import Debug.Trace

import CST
import FMD
import FMD.Extra
import Encapsulator.Common
import Encapsulator.Substitutor

---------------
-- ATTITUDES --
---------------

atts :: [Attitude]
atts = [optimism
       ,pessimism
       ,balanced]

optimism :: Attitude
optimism (Score (lb, _)) = lb

pessimism :: Attitude
pessimism (Score (_, ub)) = ub

balanced :: Attitude
balanced (Score (lb, ub)) = (lb+ub) `div` 2

----------------
-- HEURISTICS --
----------------

heurs :: Heuristics a => [Heurs a]
heurs = [ord
        ,argMod
        ,argSig
        ,objFun
        ,locVar
        ,solMod
        ,mulEnc
        ,mixI
        ,mixII]

class Heuristics a where
  ord :: Heurs a
  argMod :: Heurs a
  argSig :: Heurs a
  objFun :: Heurs a
  locVar :: Heurs a
  solMod :: Heurs a
  mulEnc :: Heurs a
  mixI :: Heurs a
  mixII :: Heurs a

instance Heuristics Vertex where
  ord vs fmd = close $ ord (open vs) fmd
  argMod vs fmd = close $ argMod (open vs) fmd
  argSig vs fmd = close $ argSig (open vs) fmd
  objFun vs fmd = close $ objFun (open vs) fmd
  locVar vs fmd = close $ locVar (open vs) fmd
  solMod vs fmd = close $ solMod (open vs) fmd
  mulEnc vs fmd = close $ mulEnc (open vs) fmd
  mixI vs fmd = close $ mixI (open vs) fmd
  mixII vs fmd = close $ mixI (open vs) fmd

open :: [Vertex] -> [Expr]
open = map $ \(Vertex e) -> e

close :: [(Expr, a)] -> [(Vertex, a)]
close = map $ \(e, s) -> (Vertex e, s)

instance Heuristics Expr where
  ord es _ = map (\e -> (e, Order)) es
  argMod es fmd = zip es' $ normalise scores
    where list = map (\e -> (e, argumentModesty e fmd [])) es
          (es', scores) = unzip list
  argSig es fmd = zip es' $ flipscales $ normalise scores
    where list = map (\e -> (e, argumentSignificance e fmd [])) es
          (es', scores) = unzip list
  objFun es fmd = zip es' $ flipscales $ normalise scores
    where list = map (\e -> (e, objectiveFunction e fmd [])) es
          (es', scores) = unzip list
  locVar es fmd = zip es' $ flipscales $ normalise scores
    where list = map (\e -> (e, localVariable e fmd [])) es
          (es', scores) = unzip list
  solMod es fmd = zip es' $ normalise scores
    where list = map (\e -> (e, solutionModesty e fmd [])) es
          (es', scores) = unzip list
  mulEnc es fmd = zip es' $ flipscales $ normalise scores
    where list = map (\e -> (e, multiEncapsulation e fmd [])) es
          (es', scores) = unzip list
  mixI es fmd = foldl1 f ss
    where ss = [argMod es fmd
               ,argSig es fmd
               ,objFun es fmd
               ,locVar es fmd
               ,solMod es fmd
               ,mulEnc es fmd]
          f vs1 vs2 = map (\((v, s1), (_, s2)) -> (v, addScore s1 s2))
                      $ zip vs1 vs2
  mixII es fmd = foldl1 f ss
    where ss = [argMod es fmd
               ,argSig es fmd
               ,objFun es fmd
               ,locVar es fmd
               ,solMod es fmd
               ,solMod es fmd
               ,solMod es fmd
               ,solMod es fmd
               ,mulEnc es fmd]
          f vs1 vs2 = map (\((v, s1), (_, s2)) -> (v, addScore s1 s2))
                      $ zip vs1 vs2


class Heuristic a where
  order :: Heur a
  argumentModesty :: Heur a
  argumentSignificance :: Heur a
  argumentSignificance' :: a -> FMD -> [Declaration] -> [(Ident, Score)]
  objectiveFunction :: Heur a
  objectiveFunction' :: a -> FMD -> [Declaration] -> [Ident]
  localVariable :: Heur a
  solutionModesty :: Heur a
  multiEncapsulation :: Heur a
  multiEncapsulation' :: Heur a

  order = error "Internal error."
  argumentModesty = error "Internal error."
  argumentSignificance = error "Internal error."
  argumentSignificance' = error "Internal error."
  objectiveFunction = error "Internal error."
  objectiveFunction' = error "Internal error."
  localVariable = error "Internal error."
  solutionModesty = error "Internal error."
  multiEncapsulation = error "Internal error."
  multiEncapsulation' = error "Internal error."

finalConstraints :: Vertex -> FMD -> [Expr]
finalConstraints v fmd1 = case insertVertex fmd1 v of
  (_, _, True) -> error "Error: missing vertex."
  (_, i, False) -> L.nub $ findConstraints' fmd3 i
    where (fmd3, _) = substitute fmd1 i ord balanced

findConstraints' :: FMD -> Int -> [Expr]
findConstraints' (FMD env vs es) i =
  if null parents -- TODO: this is incorrect in some cases!!!
    then [expr]
    else concatMap (findConstraints' (FMD env vs es)) parents
  where parents = map g $ filter f es
        f (Edge _ _ to) = to == i
        g (Edge _ from _) = from
        Vertex expr = vs !! i

mkOcc :: Ident -> [(Ident, Score)]
mkOcc i = [(i, Score (1,1))]

combineOccs :: [(Ident, Score)] -> [(Ident, Score)] -> [(Ident, Score)]
combineOccs [] occs = occs
combineOccs occs [] = occs
combineOccs x@[(i,s)] ((i',s'):occs)
  | i == i' = (i, addScore s s'):occs
  | otherwise = (i',s'):combineOccs x occs
combineOccs (occ:occs1) occs2 =
  combineOccs occs1 $ combineOccs [occ] occs2

bound :: Score -> Score
bound s@(Score (lb, ub))
  | lb < 0 = Score (0, ub)
  | otherwise = s

divScoreByZero :: Score -> Score -> Score
divScoreByZero s1 (Score (0, ub2)) = divScoreByZero s1 (Score (1, ub2))
divScoreByZero s1 (Score (ub1, 0)) = divScoreByZero s1 (Score (ub1, 1))
divScoreByZero s1 s2 = divScore s1 s2

instance Heuristic Vertex where
  order _ _ _ = Order
  argumentModesty (Vertex e) = argumentModesty e
  argumentSignificance (Vertex e) = argumentSignificance e
  argumentSignificance' (Vertex e) = argumentSignificance' e
  objectiveFunction (Vertex e) = objectiveFunction e
  objectiveFunction' (Vertex e) = objectiveFunction' e
  localVariable (Vertex e) = localVariable e
  solutionModesty (Vertex e) = solutionModesty e
  multiEncapsulation (Vertex e) = multiEncapsulation e
  multiEncapsulation' (Vertex e) = multiEncapsulation' e

instance Heuristic VarDeclItem where
  argumentSignificance'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ Nothing) fmd locs =
    argumentSignificance' bte fmd locs
  argumentSignificance'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ (Just e)) fmd locs =
    combineOccs (argumentSignificance' bte fmd locs)
                (argumentSignificance' e fmd locs)
  objectiveFunction'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ Nothing) fmd locs =
    objectiveFunction' bte fmd locs
  objectiveFunction'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ (Just e)) fmd locs =
    (++) (objectiveFunction' bte fmd locs) (objectiveFunction' e fmd locs)
  localVariable (VarDeclItem _ _ (Just _)) _ _ = score_null -- TODO: correct?
  localVariable (VarDeclItem (TiExprAndId (TiExpr bte) _) _ Nothing) fmd locs =
    localVariable bte fmd locs
  multiEncapsulation'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ Nothing) fmd locs =
    multiEncapsulation' bte fmd locs
  multiEncapsulation'
    (VarDeclItem (TiExprAndId (TiExpr bte) _) _ (Just e)) fmd locs =
    addScore (multiEncapsulation' bte fmd locs)
             (multiEncapsulation' e fmd locs)

instance Heuristic ConstraintItem where
  argumentSignificance' (ConstraintItem e) = argumentSignificance' e
  objectiveFunction' (ConstraintItem e) = objectiveFunction' e
  localVariable (ConstraintItem e) = localVariable e
  multiEncapsulation' (ConstraintItem e) = multiEncapsulation' e

instance Heuristic TiExpr where
  argumentSignificance' (TiExpr bte) = argumentSignificance' bte
  objectiveFunction' (TiExpr bte) = objectiveFunction' bte
  multiEncapsulation' (TiExpr bte) = multiEncapsulation' bte

instance Heuristic BaseTiExpr where
  argumentModesty (BaseTiExpr _ btet) = argumentModesty btet
  argumentSignificance' (BaseTiExpr _ btet) = argumentSignificance' btet
  objectiveFunction (BaseTiExpr _ btet) = objectiveFunction btet
  objectiveFunction' (BaseTiExpr _ btet) = objectiveFunction' btet
  localVariable bte@(BaseTiExpr _ btet) fmd@(FMD env _ _) locs =
    if isVar bte env locs
      then localVariable btet fmd locs
      else score_null
  solutionModesty (BaseTiExpr _ (BIdent i)) fmd@(FMD env _ _) locs =
    intToScore (toType i env locs) env locs
  solutionModesty (BaseTiExpr _ BBool) _ _ = Score (2,2)
  solutionModesty (BaseTiExpr _ BInt) _ _ = Score (int_max, int_max)
  solutionModesty (BaseTiExpr _ BFloat) _ _ = Score (int_max, int_max)
  solutionModesty (BaseTiExpr _ (BSetTiExprTail SInt)) _ _ =
    Score (int_max, int_max)
  solutionModesty (BaseTiExpr _ (BSetTiExprTail (SSet es))) _ _ =
    Score (2, 2^len) where len = min 31 $ toInteger $ length es
  solutionModesty (BaseTiExpr _ (BSetTiExprTail (SRange ne1 ne2)))
                  (FMD env _ _) locs =
    Score (2^lb, 2^ub)
    where Score (lb', ub') = sizeRange ne1 ne2 env locs
          lb = min 31 lb'
          ub = min 31 ub'
  solutionModesty (BaseTiExpr _ (BSetTiExprTail (SExpr6 (EUnion e1 e2))))
                  (FMD env _ _) locs =
    Score (min lb1 lb2, ub1 + ub2)
    where Score (lb1, ub1) = intToScore (toType e1 env locs) env locs
          Score (lb2, ub2) = intToScore (toType e2 env locs) env locs
  solutionModesty
    (BaseTiExpr _ (BArrayTiExprTail atet@(ArrayTiExprTail _ (TiExpr bte))))
    fmd@(FMD env _ _) locs =
    domSize `powScore` dimScore
    where domSize = solutionModesty bte fmd locs
          Score (lbdim, ubdim) = size atet env locs
          dimScore = Score (max 0 $ min 31 lbdim, max 0 $ min 31 ubdim)
  solutionModesty (BaseTiExpr _ (BSet es)) fmd locs =
    Score (1, ub) where ub = toInteger $ length es
  solutionModesty (BaseTiExpr _ (BRange ne1 ne2)) fmd@(FMD env _ _) locs =
    sizeRange ne1 ne2 env locs
  solutionModesty (BaseTiExpr _ (BExpr6 (EUnion e1 e2))) fmd@(FMD env _ _) locs =
    Score (min lb1 lb2, ub1 + ub2)
    where Score (lb1, ub1) = solutionModesty (toType e1 env locs) fmd locs
          Score (lb2, ub2) = solutionModesty (toType e2 env locs) fmd locs
  multiEncapsulation' (BaseTiExpr _ btet) = multiEncapsulation' btet

instance Heuristic BaseTiExprTail where
  argumentModesty (BArrayTiExprTail atet) fmd locs =
    argumentModesty atet fmd locs
  argumentModesty _ _ _ = Score (1,1)
  argumentSignificance' (BIdent i) _ _ = mkOcc i
  argumentSignificance' (BSetTiExprTail stet) fmd locs =
    argumentSignificance' stet fmd locs
  argumentSignificance' (BArrayTiExprTail atet) fmd locs =
    argumentSignificance' atet fmd locs
  argumentSignificance' (BSet es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  argumentSignificance' (BRange ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (BExpr6 e) fmd locs =
    argumentSignificance' e fmd locs
  argumentSignificance' _ _ _ = []
  objectiveFunction' (BSetTiExprTail stet) fmd locs =
    objectiveFunction' stet fmd locs
  objectiveFunction' (BArrayTiExprTail atet) fmd locs =
    objectiveFunction' atet fmd locs
  objectiveFunction' (BSet es) fmd locs =
    concatMap f es
    where f x = objectiveFunction' x fmd locs
  objectiveFunction' (BRange ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs) (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (BExpr6 e) fmd locs =
    objectiveFunction' e fmd locs
  objectiveFunction' _ _ _ = []
  localVariable (BArrayTiExprTail atet) fmd locs =
    localVariable atet fmd locs
  -- TODO: localVariable not all cases!
  localVariable _ _ _ = Score (1,1)
  multiEncapsulation' (BSetTiExprTail stet) fmd locs =
    multiEncapsulation' stet fmd locs
  multiEncapsulation' (BArrayTiExprTail atet) fmd locs =
    multiEncapsulation' atet fmd locs
  multiEncapsulation' (BSet es) fmd locs =
    foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs
  multiEncapsulation' (BRange ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (BExpr6 e) fmd locs =
    multiEncapsulation' e fmd locs
  multiEncapsulation' _ _ _ = score_null

instance Heuristic SetTiExprTail where
  argumentSignificance' SInt _ _ = []
  argumentSignificance' (SSet es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  argumentSignificance' (SRange ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (SExpr6 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' SInt _ _ = []
  objectiveFunction' (SSet es) fmd locs =
    concatMap f es
    where f x = objectiveFunction' x fmd locs
  objectiveFunction' (SRange ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs) (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (SExpr6 e) fmd locs =
    objectiveFunction' e fmd locs
  multiEncapsulation' SInt _ _ = score_null
  multiEncapsulation' (SSet es) fmd locs =
    foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs
  multiEncapsulation' (SRange ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (SExpr6 e) fmd locs =
    multiEncapsulation' e fmd locs

instance Heuristic ArrayTiExprTail where
  argumentModesty atet (FMD env _ _) = size atet env
  argumentSignificance' (ArrayTiExprTail tes te) fmd locs =
    combineOccs (argumentSignificance' te fmd locs)
                (foldl combineOccs [] $ map f tes)
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (ArrayTiExprTail tes te) fmd locs =
    (++) (objectiveFunction' te fmd locs) (concatMap f tes)
    where f x = objectiveFunction' x fmd locs
  localVariable atet (FMD env _ _) = size atet env
  multiEncapsulation' (ArrayTiExprTail tes te) fmd locs =
    addScore (multiEncapsulation' te fmd locs)
             (foldl addScore score_null $ map f tes)
    where f x = multiEncapsulation' x fmd locs

instance Heuristic Expr where
  order _ _ _ = Order
  argumentModesty e fmd locs = foldl f score_null (identifiers e)
    where f score i = addScore score $ bound $ argumentModesty i fmd locs
  argumentSignificance e fmd@(FMD env _ _) locs =
    f . g $ argumentSignificance' e fmd locs
    where f [] = score_null
          f ((i,s):occs) = addScore s $ f occs
          g [] = []
          g ((i,s):occs) = (i,z):g occs
            where x = sizeIdentBTE i env locs
                  y = mulScore (subScoreNonNeg s x) $ Score (100,100)
                  z = divScoreByZero y x
  argumentSignificance' (Expr e) = argumentSignificance' e
  objectiveFunction e fmd@(FMD env@(Environment _ _ _ _ si) _ _) locs =
    Score (num, num)
    where cand = L.nub $ concatMap f es
          es = finalConstraints (Vertex e) fmd
          f x = objectiveFunction' x fmd locs
          obj = filter (\x-> isVar x env locs) $ identifiers si
          num = fromIntegral $ length (obj `L.intersect` cand)
  objectiveFunction' (Expr e) = objectiveFunction' e
  localVariable (Expr e) = localVariable e
  solutionModesty e fmd locs = foldl f (Score (1,1)) (identifiers e)
    where f score i = mulScore score $ bound $ solutionModesty i fmd locs
  multiEncapsulation e fmd locs =
    foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs
          es = finalConstraints (Vertex e) fmd
  multiEncapsulation' (Expr e) = multiEncapsulation' e

instance Heuristic Expr12 where
  argumentSignificance' (EEquivalence e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr11 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EEquivalence e1 e2) fmd locs =
    objectiveFunction' e1 fmd locs ++ objectiveFunction' e2 fmd locs
  objectiveFunction' (EExpr11 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EEquivalence e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr11 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EEquivalence e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr11 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr11 where
  argumentSignificance' (ELImplies e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ERImplies e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr10 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (ELImplies e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ERImplies e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr10 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (ELImplies e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ERImplies e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr10 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (ELImplies e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ERImplies e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr10 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr10 where
  argumentSignificance' (EOr e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EXor e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr9 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EOr e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EXor e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr9 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EOr e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EXor e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr9 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EOr e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EXor e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr9 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr9 where
  argumentSignificance' (EAnd e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr8 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EAnd e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr8 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EAnd e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr8 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EAnd e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr8 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr8 where
  argumentSignificance' (ELt e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EGt e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ELeq e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EGeq e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EEq e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EEqEq e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ENeq e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr7 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (ELt e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EGt e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ELeq e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EGeq e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EEq e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EEqEq e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ENeq e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr7 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (ELt e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EGt e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ELeq e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EGeq e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EEq e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EEqEq e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ENeq e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr7 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (ELt e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EGt e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ELeq e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EGeq e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EEq e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EEqEq e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ENeq e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr7 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr7 where
  argumentSignificance' (EIn e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ESubset e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ESuperset e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr6 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EIn e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ESubset e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ESuperset e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr6 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EIn e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ESubset e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ESuperset e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr6 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EIn e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ESubset e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ESuperset e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr6 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr6 where
  argumentSignificance' (EUnion e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EDiff e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ESymDiff e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr5 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EUnion e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EDiff e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ESymDiff e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr5 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EUnion e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EDiff e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ESymDiff e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr5 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EUnion e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EDiff e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ESymDiff e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr5 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr5 where
  argumentSignificance' (EEllipsis e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr4 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EEllipsis e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr4 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EEllipsis e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr4 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EEllipsis e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr4 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr4 where
  argumentSignificance' (EPlus e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EMinus e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr3 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EPlus e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EMinus e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr3 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EPlus e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EMinus e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr3 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EPlus e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EMinus e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr3 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr3 where
  argumentSignificance' (EStar e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EDiv e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EMod e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (ESlash e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EIntersect e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr2 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EStar e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EDiv e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EMod e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (ESlash e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EIntersect e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr2 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EStar e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EDiv e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EMod e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (ESlash e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EIntersect e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr2 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EStar e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EDiv e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EMod e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (ESlash e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EIntersect e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr2 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr2 where
  argumentSignificance' (EPlusPlus e1 e2) fmd locs =
    combineOccs (argumentSignificance' e1 fmd locs)
                (argumentSignificance' e2 fmd locs)
  argumentSignificance' (EExpr1 e) fmd locs =
    argumentSignificance' e fmd locs
  objectiveFunction' (EPlusPlus e1 e2) fmd locs =
    (++) (objectiveFunction' e1 fmd locs) (objectiveFunction' e2 fmd locs)
  objectiveFunction' (EExpr1 e) fmd locs = objectiveFunction' e fmd locs
  localVariable (EPlusPlus e1 e2) fmd locs =
    addScore (localVariable e1 fmd locs) (localVariable e2 fmd locs)
  localVariable (EExpr1 e) fmd locs = localVariable e fmd locs
  multiEncapsulation' (EPlusPlus e1 e2) fmd locs =
    addScore (multiEncapsulation' e1 fmd locs) (multiEncapsulation' e2 fmd locs)
  multiEncapsulation' (EExpr1 e) fmd locs = multiEncapsulation' e fmd locs

instance Heuristic Expr1 where
  argumentSignificance' (EIdent _ e ea) fmd locs =
    combineOccs (argumentSignificance' e fmd locs)
                (argumentSignificance' ea fmd locs)
  argumentSignificance' (EExprAtom ea) fmd locs =
    argumentSignificance' ea fmd locs
  objectiveFunction' (EIdent _ e ea) fmd locs =
    (++) (objectiveFunction' e fmd locs) (objectiveFunction' ea fmd locs)
  objectiveFunction' (EExprAtom ea) fmd locs = objectiveFunction' ea fmd locs
  localVariable (EIdent _ e ea) fmd locs =
    addScore (localVariable e fmd locs) (localVariable ea fmd locs)
  localVariable (EExprAtom ea) fmd locs = localVariable ea fmd locs
  multiEncapsulation' (EIdent _ e ea) fmd locs =
    addScore (multiEncapsulation' e fmd locs) (multiEncapsulation' ea fmd locs)
  multiEncapsulation' (EExprAtom ea) fmd locs = multiEncapsulation' ea fmd locs

instance Heuristic ExprAtom where
  argumentSignificance' (ExprAtom eah eat _) fmd locs =
    combineOccs (argumentSignificance' eah fmd locs)
                (argumentSignificance' eat fmd locs)
  objectiveFunction' (ExprAtom eah eat _) fmd locs =
    (++) (objectiveFunction' eah fmd locs) (objectiveFunction' eat fmd locs)
  localVariable (ExprAtom eah eat _) fmd locs =
    addScore (localVariable eah fmd locs) (localVariable eat fmd locs)
  multiEncapsulation' (ExprAtom eah eat _) fmd locs =
    addScore (multiEncapsulation' eah fmd locs) (multiEncapsulation' eat fmd locs)

instance Heuristic ExprAtomHead where
  argumentSignificance' (EBuiltinUnOp _ ea) fmd locs =
    argumentSignificance' ea fmd locs
  argumentSignificance' (EExpr e) fmd locs =
    argumentSignificance' e fmd locs
  argumentSignificance' (EIdentOrQuotedOp ioqo) fmd locs =
    argumentSignificance' ioqo fmd locs
  argumentSignificance' (EBoolLiteral _) _ _ = []
  argumentSignificance' (EIntLiteral _) _ _ = []
  argumentSignificance' (EFloatLiteral _) _ _ = []
  argumentSignificance' (ESetLiteral sl) fmd locs =
    argumentSignificance' sl fmd locs
  argumentSignificance' (ESetComp sc) fmd locs =
    argumentSignificance' sc fmd locs
  argumentSignificance' (EArrayLiteral al) fmd locs =
    argumentSignificance' al fmd locs
  argumentSignificance' (EArrayComp ac) fmd locs =
    argumentSignificance' ac fmd locs
  argumentSignificance' (EIfThenElseExpr itee) fmd locs =
    argumentSignificance' itee fmd locs
  argumentSignificance' (ELetExpr le) fmd locs =
    argumentSignificance' le fmd locs
  argumentSignificance' (ECallExpr ce) fmd locs =
    argumentSignificance' ce fmd locs
  argumentSignificance' (EGenCallExpr gce) fmd locs =
    argumentSignificance' gce fmd locs
  objectiveFunction' (EBuiltinUnOp _ ea) fmd locs =
    objectiveFunction' ea fmd locs
  objectiveFunction' (EExpr e) fmd locs =
    objectiveFunction' e fmd locs
  objectiveFunction' (EIdentOrQuotedOp ioqo) fmd locs =
    objectiveFunction' ioqo fmd locs
  objectiveFunction' (EBoolLiteral _) _ _ = []
  objectiveFunction' (EIntLiteral _) _ _ = []
  objectiveFunction' (EFloatLiteral _) _ _ = []
  objectiveFunction' (ESetLiteral sl) fmd locs =
    objectiveFunction' sl fmd locs
  objectiveFunction' (ESetComp sc) fmd locs =
    objectiveFunction' sc fmd locs
  objectiveFunction' (EArrayLiteral al) fmd locs =
    objectiveFunction' al fmd locs
  objectiveFunction' (EArrayComp ac) fmd locs =
    objectiveFunction' ac fmd locs
  objectiveFunction' (EIfThenElseExpr itee) fmd locs =
    objectiveFunction' itee fmd locs
  objectiveFunction' (ELetExpr le) fmd locs =
    objectiveFunction' le fmd locs
  objectiveFunction' (ECallExpr ce) fmd locs =
    objectiveFunction' ce fmd locs
  objectiveFunction' (EGenCallExpr gce) fmd locs =
    objectiveFunction' gce fmd locs
  localVariable (EBuiltinUnOp _ ea) fmd locs =
    localVariable ea fmd locs
  localVariable (EExpr e) fmd locs =
    localVariable e fmd locs
  localVariable (EIdentOrQuotedOp ioqo) fmd locs =
    localVariable ioqo fmd locs
  localVariable (EBoolLiteral _) _ _ = score_null
  localVariable (EIntLiteral _) _ _ = score_null
  localVariable (EFloatLiteral _) _ _ = score_null
  localVariable (ESetLiteral sl) fmd locs =
    localVariable sl fmd locs
  localVariable (ESetComp sc) fmd locs =
    localVariable sc fmd locs
  localVariable (EArrayLiteral al) fmd locs =
    localVariable al fmd locs
  localVariable (EArrayComp ac) fmd locs =
    localVariable ac fmd locs
  localVariable (EIfThenElseExpr itee) fmd locs =
    localVariable itee fmd locs
  localVariable (ELetExpr le) fmd locs =
    localVariable le fmd locs
  localVariable (ECallExpr ce) fmd locs =
    localVariable ce fmd locs
  localVariable (EGenCallExpr gce) fmd locs =
    localVariable gce fmd locs
  multiEncapsulation' (EBuiltinUnOp _ ea) fmd locs =
    multiEncapsulation' ea fmd locs
  multiEncapsulation' (EExpr e) fmd locs =
    multiEncapsulation' e fmd locs
  multiEncapsulation' (EIdentOrQuotedOp ioqo) fmd locs =
    multiEncapsulation' ioqo fmd locs
  multiEncapsulation' (EBoolLiteral _) _ _ = score_null
  multiEncapsulation' (EIntLiteral _) _ _ = score_null
  multiEncapsulation' (EFloatLiteral _) _ _ = score_null
  multiEncapsulation' (ESetLiteral sl) fmd locs =
    multiEncapsulation' sl fmd locs
  multiEncapsulation' (ESetComp sc) fmd locs =
    multiEncapsulation' sc fmd locs
  multiEncapsulation' (EArrayLiteral al) fmd locs =
    multiEncapsulation' al fmd locs
  multiEncapsulation' (EArrayComp ac) fmd locs =
    multiEncapsulation' ac fmd locs
  multiEncapsulation' (EIfThenElseExpr itee) fmd locs =
    multiEncapsulation' itee fmd locs
  multiEncapsulation' (ELetExpr le) fmd locs =
    multiEncapsulation' le fmd locs
  multiEncapsulation' (ECallExpr ce) fmd locs =
    multiEncapsulation' ce fmd locs
  multiEncapsulation' (EGenCallExpr gce) fmd locs =
    multiEncapsulation' gce fmd locs

instance Heuristic ExprAtomTail where
  argumentSignificance' EATNothing _ _ = []
  argumentSignificance' (ExprAtomTail aat eat) fmd locs =
    combineOccs (argumentSignificance' aat fmd locs)
                (argumentSignificance' eat fmd locs)
  objectiveFunction' EATNothing _ _ = []
  objectiveFunction' (ExprAtomTail aat eat) fmd locs =
    (++) (objectiveFunction' aat fmd locs) (objectiveFunction' eat fmd locs)
  localVariable EATNothing _ _ = score_null
  localVariable (ExprAtomTail aat eat) fmd locs =
    addScore (localVariable aat fmd locs) (localVariable eat fmd locs)
  multiEncapsulation' EATNothing _ _ = score_null
  multiEncapsulation' (ExprAtomTail aat eat) fmd locs =
    addScore (multiEncapsulation' aat fmd locs)
             (multiEncapsulation' eat fmd locs)

instance Heuristic NumExpr where
  argumentSignificance' (NumExpr ne) = argumentSignificance' ne
  objectiveFunction' (NumExpr ne) = objectiveFunction' ne
  multiEncapsulation' (NumExpr ne) = multiEncapsulation' ne

instance Heuristic NumExpr4 where
  argumentSignificance' (NPlus ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NMinus ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NNumExpr3 ne) fmd locs =
    argumentSignificance' ne fmd locs
  objectiveFunction' (NPlus ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs) (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NMinus ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs) (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NNumExpr3 ne) fmd locs =
    objectiveFunction' ne fmd locs
  multiEncapsulation' (NPlus ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NMinus ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NNumExpr3 ne) fmd locs =
    multiEncapsulation' ne fmd locs

instance Heuristic NumExpr3 where
  argumentSignificance' (NStar ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NDiv ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NMod ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NSlash ne1 ne2) fmd locs =
    combineOccs (argumentSignificance' ne1 fmd locs)
                (argumentSignificance' ne2 fmd locs)
  argumentSignificance' (NNumExpr1 ne) fmd locs =
    argumentSignificance' ne fmd locs
  objectiveFunction' (NStar ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs) (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NDiv ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs)  (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NMod ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs)  (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NSlash ne1 ne2) fmd locs =
    (++) (objectiveFunction' ne1 fmd locs)  (objectiveFunction' ne2 fmd locs)
  objectiveFunction' (NNumExpr1 ne) fmd locs =
    objectiveFunction' ne fmd locs
  multiEncapsulation' (NStar ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NDiv ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NMod ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NSlash ne1 ne2) fmd locs =
    addScore (multiEncapsulation' ne1 fmd locs)
             (multiEncapsulation' ne2 fmd locs)
  multiEncapsulation' (NNumExpr1 ne) fmd locs =
    multiEncapsulation' ne fmd locs

instance Heuristic NumExpr1 where
  argumentSignificance' (NIdent _ ne nea) fmd locs =
    combineOccs (argumentSignificance' ne fmd locs)
                (argumentSignificance' nea fmd locs)
  argumentSignificance' (NNumExprAtom ne) fmd locs =
    argumentSignificance' ne fmd locs
  objectiveFunction' (NIdent _ ne nea) fmd locs =
    (++) (objectiveFunction' ne fmd locs) (objectiveFunction' nea fmd locs)
  objectiveFunction' (NNumExprAtom ne) fmd locs =
    objectiveFunction' ne fmd locs
  multiEncapsulation' (NIdent _ ne nea) fmd locs =
    addScore (multiEncapsulation' ne fmd locs)
             (multiEncapsulation' nea fmd locs)
  multiEncapsulation' (NNumExprAtom ne) fmd locs =
    multiEncapsulation' ne fmd locs

instance Heuristic NumExprAtom where
  argumentSignificance' (NumExprAtom neah eat _) fmd locs =
    combineOccs (argumentSignificance' neah fmd locs)
                (argumentSignificance' eat fmd locs)
  objectiveFunction' (NumExprAtom neah eat _) fmd locs =
    (++) (objectiveFunction' neah fmd locs) (objectiveFunction' eat fmd locs)
  multiEncapsulation' (NumExprAtom neah eat _) fmd locs =
    addScore (multiEncapsulation' neah fmd locs)
             (multiEncapsulation' eat fmd locs)

instance Heuristic NumExprAtomHead where
  argumentSignificance' (NBuiltinNumUnOp _ ea) fmd locs =
    argumentSignificance' ea fmd locs
  argumentSignificance' (NNumExpr e) fmd locs =
    argumentSignificance' e fmd locs
  argumentSignificance' (NIdentOrQuotedOp ioqo) fmd locs =
    argumentSignificance' ioqo fmd locs
  argumentSignificance' (NIntLiteral _) _ _ = []
  argumentSignificance' (NFloatLiteral _) _ _ = []
  argumentSignificance' (NIfThenElseExpr itee) fmd locs =
    argumentSignificance' itee fmd locs
  argumentSignificance' (NLetExpr le) fmd locs =
    argumentSignificance' le fmd locs
  argumentSignificance' (NCallExpr ce) fmd locs =
    argumentSignificance' ce fmd locs
  argumentSignificance' (NGenCallExpr gce) fmd locs =
    argumentSignificance' gce fmd locs
  objectiveFunction' (NBuiltinNumUnOp _ ea) fmd locs =
    objectiveFunction' ea fmd locs
  objectiveFunction' (NNumExpr e) fmd locs =
    objectiveFunction' e fmd locs
  objectiveFunction' (NIdentOrQuotedOp ioqo) fmd locs =
    objectiveFunction' ioqo fmd locs
  objectiveFunction' (NIntLiteral _) _ _ = []
  objectiveFunction' (NFloatLiteral _) _ _ = []
  objectiveFunction' (NIfThenElseExpr itee) fmd locs =
    objectiveFunction' itee fmd locs
  objectiveFunction' (NLetExpr le) fmd locs =
    objectiveFunction' le fmd locs
  objectiveFunction' (NCallExpr ce) fmd locs =
    objectiveFunction' ce fmd locs
  objectiveFunction' (NGenCallExpr gce) fmd locs =
    objectiveFunction' gce fmd locs
  localVariable (NBuiltinNumUnOp _ ea) fmd locs =
    localVariable ea fmd locs
  localVariable (NNumExpr e) fmd locs =
    localVariable e fmd locs
  localVariable (NIdentOrQuotedOp ioqo) fmd locs =
    localVariable ioqo fmd locs
  localVariable (NIntLiteral _) _ _ = score_null
  localVariable (NFloatLiteral _) _ _ = score_null
  localVariable (NIfThenElseExpr itee) fmd locs =
    localVariable itee fmd locs
  localVariable (NLetExpr le) fmd locs =
    localVariable le fmd locs
  localVariable (NCallExpr ce) fmd locs =
    localVariable ce fmd locs
  localVariable (NGenCallExpr gce) fmd locs =
    localVariable gce fmd locs
  multiEncapsulation' (NBuiltinNumUnOp _ ea) fmd locs =
    multiEncapsulation' ea fmd locs
  multiEncapsulation' (NNumExpr e) fmd locs =
    multiEncapsulation' e fmd locs
  multiEncapsulation' (NIdentOrQuotedOp ioqo) fmd locs =
    multiEncapsulation' ioqo fmd locs
  multiEncapsulation' (NIntLiteral _) _ _ = score_null
  multiEncapsulation' (NFloatLiteral _) _ _ = score_null
  multiEncapsulation' (NIfThenElseExpr itee) fmd locs =
    multiEncapsulation' itee fmd locs
  multiEncapsulation' (NLetExpr le) fmd locs =
    multiEncapsulation' le fmd locs
  multiEncapsulation' (NCallExpr ce) fmd locs =
    multiEncapsulation' ce fmd locs
  multiEncapsulation' (NGenCallExpr gce) fmd locs =
    multiEncapsulation' gce fmd locs

instance Heuristic SetLiteral where
  argumentSignificance' (SetLiteral es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (SetLiteral es) fmd locs =
    concatMap (\x -> objectiveFunction' x fmd locs) es
  localVariable (SetLiteral es) fmd locs =
    foldl addScore score_null $ map (\x -> localVariable x fmd locs) es
  multiEncapsulation' (SetLiteral es) fmd locs =
    foldl addScore score_null $ map (\x -> multiEncapsulation' x fmd locs) es

instance Heuristic SetComp where
  argumentSignificance' (SetComp e ct) fmd@(FMD env _ _) locs =
    combineOccs (map f $ argumentSignificance' e fmd locs1)
                (argumentSignificance' ct fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f (i,s) = (i,mulScore s $ sizeComp ct env locs1)
  objectiveFunction' (SetComp e ct) fmd@(FMD env _ _) locs =
    (++) (objectiveFunction' e fmd locs1) (objectiveFunction' ct fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
  localVariable (SetComp e ct) fmd@(FMD env _ _) locs =
    let locs1 = ctToLocalDecls ct env locs ++ locs
    in addScore (localVariable e fmd locs1) (localVariable ct fmd locs1)
  multiEncapsulation' (SetComp e ct) fmd@(FMD env _ _) locs =
    addScore (f $ multiEncapsulation' e fmd locs1)
             (multiEncapsulation' ct fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f s = mulScore s $ sizeComp ct env locs1

sizeComp :: CompTail -> Environment -> [Declaration] -> Score
sizeComp ct env locs =
  foldl addScore score_null $ map f $ ctToLocalDecls ct env locs
  where f (Declaration bte _) = sizeBTE bte env locs

instance Heuristic CompTail where
  argumentSignificance' (CompTail gs Nothing) fmd locs =
    foldl combineOccs [] $ map (\x-> argumentSignificance' x fmd locs) gs
  argumentSignificance' (CompTail gs (Just e)) fmd locs =
    combineOccs (argumentSignificance' e fmd locs)
                (foldl combineOccs [] $ map f gs)
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (CompTail gs Nothing) fmd locs =
    concatMap (\x-> objectiveFunction' x fmd locs) gs
  objectiveFunction' (CompTail gs (Just e)) fmd locs =
    (++) (objectiveFunction' e fmd locs) (concatMap f gs)
    where f x = objectiveFunction' x fmd locs
  localVariable (CompTail gs Nothing) fmd locs =
    foldl addScore score_null $ map (\x -> localVariable x fmd locs) gs
  localVariable (CompTail gs (Just e)) fmd locs =
    let scores = foldl addScore score_null
                 $ map (\x -> localVariable x fmd locs) gs
    in addScore scores (localVariable e fmd locs)
  multiEncapsulation' (CompTail gs Nothing) fmd locs =
    foldl addScore score_null $ map (\x-> multiEncapsulation' x fmd locs) gs
  multiEncapsulation' (CompTail gs (Just e)) fmd locs =
    addScore (multiEncapsulation' e fmd locs)
             (foldl addScore score_null $ map f gs)
    where f x = multiEncapsulation' x fmd locs

instance Heuristic Generator where
  argumentSignificance' (Generator _ e) = argumentSignificance' e
  objectiveFunction' (Generator _ e) = objectiveFunction' e
  localVariable (Generator _ e) = localVariable e
  multiEncapsulation' (Generator _ e) = multiEncapsulation' e

instance Heuristic ArrayLiteral where
  argumentSignificance' (ArrayLiteral es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (ArrayLiteral es) fmd locs =
    concatMap f es
    where f x = objectiveFunction' x fmd locs
  localVariable (ArrayLiteral es) fmd locs =
    foldl addScore score_null $ map (\x -> localVariable x fmd locs) es
  multiEncapsulation' (ArrayLiteral es) fmd locs =
    foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs

instance Heuristic ArrayComp where
  argumentSignificance' (ArrayComp e ct) fmd@(FMD env _ _) locs =
    combineOccs (argumentSignificance' ct fmd locs1)
                (map f $ argumentSignificance' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f (i,s) = (i,mulScore s $ sizeComp ct env locs1)
  objectiveFunction' (ArrayComp e ct) fmd@(FMD env _ _) locs =
    (++) (objectiveFunction' ct fmd locs1) (objectiveFunction' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
  localVariable (ArrayComp e ct) fmd@(FMD env _ _) locs =
    let locs1 = ctToLocalDecls ct env locs ++ locs
    in addScore (localVariable e fmd locs1) (localVariable ct fmd locs1)
  multiEncapsulation' (ArrayComp e ct) fmd@(FMD env _ _) locs =
    addScore (multiEncapsulation' ct fmd locs1)
             (f $ multiEncapsulation' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f s = mulScore s $ sizeComp ct env locs1

instance Heuristic ArrayAccessTail where
  argumentSignificance' (ArrayAccessTail es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (ArrayAccessTail es) fmd locs =
    concatMap f es
    where f x = objectiveFunction' x fmd locs
  localVariable (ArrayAccessTail es) fmd locs =
    foldl addScore score_null $ map (\x -> localVariable x fmd locs) es
  multiEncapsulation' (ArrayAccessTail es) fmd locs =
    foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs

instance Heuristic IfThenElseExpr where
  argumentSignificance' (IfThenElseExpr c e ces ee) fmd locs =
    foldl combineOccs [] [f c, f e, ces1, f ee]
    where f x = argumentSignificance' x fmd locs
          ces1 = foldl combineOccs [] $ concatMap (\(a,b) -> [f a, f b]) ces
  objectiveFunction' (IfThenElseExpr c e ces ee) fmd locs =
    concat [f c, f e, ces1, f ee]
    where f x = objectiveFunction' x fmd locs
          ces1 = concatMap (\(a,b) -> f a ++ f b) ces
  localVariable (IfThenElseExpr c e ces ee) fmd locs =
    let ces1 = foldl addScore score_null $ concatMap (\(a,b) -> [f a, f b]) ces
    in foldl addScore score_null [f c, f e, ces1, f ee]
    where f x = localVariable x fmd locs
  multiEncapsulation' (IfThenElseExpr c e ces ee) fmd locs =
    foldl addScore score_null [f c, f e, ces1, f ee]
    where f x = multiEncapsulation' x fmd locs
          ces1 = foldl addScore score_null $ concatMap (\(a,b) -> [f a,f b]) ces

instance Heuristic CallExpr where
  argumentSignificance' (CallExpr _ es) fmd locs =
    foldl combineOccs [] $ map f es
    where f x = argumentSignificance' x fmd locs
  objectiveFunction' (CallExpr i es) fmd locs
    | i == IIdent (Ident "PREDICATE_0") = -- TODO: make this dynamic!
        concatMap identifiers es
    | otherwise =
        concatMap f es
    where f x = objectiveFunction' x fmd locs
  localVariable (CallExpr _ es) fmd locs =
    foldl addScore score_null $ map (\x -> localVariable x fmd locs) es
  multiEncapsulation' (CallExpr i es) fmd locs
    | i == IIdent (Ident "PREDICATE_0") = -- TODO: make this dynamic!
        Score (1,1)
    | otherwise =
        foldl addScore score_null $ map f es
    where f x = multiEncapsulation' x fmd locs

instance Heuristic LetExpr where
  argumentSignificance' (LetExpr lis e) fmd locs =
    combineOccs (argumentSignificance' e fmd locs1)
                (foldl combineOccs [] $ map f lis)
    where locs1 = lisToLocalDecls lis ++ locs
          f x = argumentSignificance' x fmd locs1
  objectiveFunction' (LetExpr lis e) fmd locs =
    (++) (objectiveFunction' e fmd locs1) (concatMap f lis)
    where locs1 = lisToLocalDecls lis ++ locs
          f x = objectiveFunction' x fmd locs1
  localVariable (LetExpr lis e) fmd locs =
    let locs1 = lisToLocalDecls lis ++ locs
        score1 = foldl addScore score_null
               $ map (\x -> localVariable x fmd locs1) lis
    in addScore score1 (localVariable e fmd locs1)
  multiEncapsulation' (LetExpr lis e) fmd locs =
    addScore (multiEncapsulation' e fmd locs1)
             (foldl addScore score_null $ map f lis)
    where locs1 = lisToLocalDecls lis ++ locs
          f x = multiEncapsulation' x fmd locs1

instance Heuristic LetItem where
  argumentSignificance' (LConstraintItem ci) fmd locs =
    argumentSignificance' ci fmd locs
  argumentSignificance' (LVarDeclItem vdi) fmd locs =
    argumentSignificance' vdi fmd locs
  objectiveFunction' (LConstraintItem ci) fmd locs =
    objectiveFunction' ci fmd locs
  objectiveFunction' (LVarDeclItem vdi) fmd locs =
    objectiveFunction' vdi fmd locs
  localVariable (LConstraintItem ci) fmd locs =
    localVariable ci fmd locs
  localVariable (LVarDeclItem vdi) fmd locs =
    localVariable vdi fmd locs
  multiEncapsulation' (LConstraintItem ci) fmd locs =
    multiEncapsulation' ci fmd locs
  multiEncapsulation' (LVarDeclItem vdi) fmd locs =
    multiEncapsulation' vdi fmd locs

instance Heuristic GenCallExpr where
  argumentSignificance' (GenCallExpr _ ct e) fmd@(FMD env _ _) locs =
    combineOccs (argumentSignificance' ct fmd locs1)
                (map f $ argumentSignificance' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f (i,s) = (i,mulScore s $ sizeComp ct env locs1)
  objectiveFunction' (GenCallExpr _ ct e) fmd@(FMD env _ _) locs =
    (++) (objectiveFunction' ct fmd locs1) (objectiveFunction' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
  localVariable (GenCallExpr _ ct e) fmd@(FMD env _ _) locs =
    let locs1 = ctToLocalDecls ct env locs ++ locs
    in addScore (localVariable ct fmd locs1) (localVariable e fmd locs1)
  multiEncapsulation' (GenCallExpr _ ct e) fmd@(FMD env _ _) locs =
    addScore (multiEncapsulation' ct fmd locs1)
             (f $ multiEncapsulation' e fmd locs1)
    where locs1 = ctToLocalDecls ct env locs ++ locs
          f s = mulScore s $ sizeComp ct env locs1

sizeIdentBTE :: Ident -> Environment -> [Declaration] -> Score
sizeIdentBTE i env locs =
  case findDecl env1 i of
    Just (Declaration (BaseTiExpr _ btet) _) -> case btet of
      BArrayTiExprTail atet -> size atet env locs
      _ -> Score (1,1)
    Nothing -> error $ "Error! Declaration for `" ++ show i ++ "' not found."
  where env1 = foldl (flip insertDeclaration) env locs

instance Heuristic Ident where
  argumentModesty i fmd@(FMD env _ _) locs = case findDecl env1 i of
    Just decl -> if decl `elem` locs
                   then score_null
                   else argumentModesty decl fmd locs
    Nothing -> error ("Error! Declaration for `" ++ show i ++ "' not found." ++
                      "\nWith Env: " ++ show env ++
                      "\n  Locals: " ++ show locs)
    where env1 = foldl (flip insertDeclaration) env locs
  argumentSignificance' i _ locs =
    case findDecl env1 i of
      Just _ -> []
      Nothing -> mkOcc i
    where env1 = foldl (flip insertDeclaration) emptyEnv locs
  objectiveFunction' _ _ _ = []
  localVariable _ _ _ = score_null
  solutionModesty i fmd@(FMD env _ _) locs = case findDecl env1 i of
    Just decl -> if decl `elem` locs
                   then score_null
                   else solutionModesty decl fmd locs
    Nothing -> error $ "Internal error! Declaration for `" ++ show i
                                             ++ "' not found."
    where env1 = foldl (flip insertDeclaration) env locs
  multiEncapsulation' _ _ _ = score_null

instance Heuristic IdentOrQuotedOp where
  argumentSignificance' (IIdent i) = argumentSignificance' i
  objectiveFunction' (IIdent i) = objectiveFunction' i
  localVariable (IIdent i) = localVariable i
  multiEncapsulation' (IIdent i) = multiEncapsulation' i

instance Heuristic Declaration where
  argumentModesty (Declaration bte _) = argumentModesty bte
  solutionModesty (Declaration bte _) = solutionModesty bte

------------------------
-- MATCHING HEURISTIC --
------------------------

class EasyMatch a where
  easyMatch :: a -> a -> Bool

instance EasyMatch Expr where
  easyMatch (Expr e1) (Expr e2) = easyMatch e1 e2

instance EasyMatch Expr12 where
  easyMatch (EEquivalence e11 e12) (EEquivalence e21 e22) = True
  easyMatch (EExpr11 e1) (EExpr11 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr11 where
  easyMatch (ELImplies e11 e12) (ELImplies e21 e22) = True
  easyMatch (ERImplies e11 e12) (ERImplies e21 e22) = True
  easyMatch (EExpr10 e1) (EExpr10 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr10 where
  easyMatch (EOr e11 e12) (EOr e21 e22) = True
  easyMatch (EXor e11 e12) (EXor e21 e22) = True
  easyMatch (EExpr9 e1) (EExpr9 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr9 where
  easyMatch (EAnd e11 e12) (EAnd e21 e22) = True
  easyMatch (EExpr8 e1) (EExpr8 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr8 where
  easyMatch (EGt e11 e12) e =
    easyMatch (ELt e12 e11) e
  easyMatch e (EGt e11 e12) =
    easyMatch e (ELt e12 e11)
  easyMatch (EGeq e11 e12) e =
    easyMatch (ELeq e12 e11) e
  easyMatch e (EGeq e11 e12) =
    easyMatch e (ELeq e12 e11)
  easyMatch (EEqEq e11 e12) e =
    easyMatch (EEq e12 e11) e
  easyMatch e (EEqEq e11 e12) =
    easyMatch e (EEq e12 e11)

  easyMatch (ELt e11 e12) (ELt e21 e22) = True
  easyMatch (ELeq e11 e12) (ELeq e21 e22) = True
  easyMatch (EEq e11 e12) (EEq e21 e22) = True
  easyMatch (ENeq e11 e12) (ENeq e21 e22) = True
  easyMatch (EExpr7 e1) (EExpr7 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr7 where
  easyMatch (EIn e11 e12) (EIn e21 e22) = True
  easyMatch (ESubset e11 e12) (ESubset e21 e22) = True
  easyMatch (ESuperset e11 e12) (ESuperset e21 e22) = True
  easyMatch (EExpr6 e1) (EExpr6 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr6 where
  easyMatch (EUnion e11 e12) (EUnion e21 e22) = True
  easyMatch (EDiff e11 e12) (EDiff e21 e22) = True
  easyMatch (ESymDiff e11 e12) (ESymDiff e21 e22) = True
  easyMatch (EExpr5 e1) (EExpr5 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr5 where
  easyMatch (EEllipsis e11 e12) (EEllipsis e21 e22) = True
  easyMatch (EExpr4 e1) (EExpr4 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr4 where
  easyMatch (EPlus e11 e12) (EPlus e21 e22) = True
  easyMatch (EMinus e11 e12) (EMinus e21 e22) = True
  easyMatch (EExpr3 e1) (EExpr3 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr3 where
  easyMatch (EStar e11 e12) (EStar e21 e22) = True
  easyMatch (EDiv e11 e12) (EDiv e21 e22) = True
  easyMatch (EMod e11 e12) (EMod e21 e22) = True
  easyMatch (ESlash e11 e12) (ESlash e21 e22) = True
  easyMatch (EIntersect e11 e12) (EIntersect e21 e22) = True
  easyMatch (EExpr2 e1) (EExpr2 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr2 where
  easyMatch (EPlusPlus e11 e12) (EPlusPlus e21 e22) = True
  easyMatch (EExpr1 e1) (EExpr1 e2) = easyMatch e1 e2
  easyMatch _ _ = False

instance EasyMatch Expr1 where
  easyMatch (EIdent i1 e1 ea1) (EIdent i2 e2 ea2) = True
  easyMatch (EExprAtom ea1) (EExprAtom ea2) = easyMatch ea1 ea2
  easyMatch _ _ = False

instance EasyMatch ExprAtom where
  easyMatch (ExprAtom eah1 eat1 _) (ExprAtom eah2 eat2 _) =
    easyMatch eah1 eah2 && easyMatch eat1 eat2

instance EasyMatch ExprAtomHead where
  easyMatch (EBuiltinUnOp buo1 ea1) (EBuiltinUnOp buo2 ea2) = True
  easyMatch (EExpr e1) (EExpr e2) = True
  easyMatch (EIdentOrQuotedOp ioqo1) (EIdentOrQuotedOp ioqo2) = True
  easyMatch (EBoolLiteral bl1) (EBoolLiteral bl2) = True
  easyMatch (EIntLiteral il1) (EIntLiteral il2) = True
  easyMatch (EFloatLiteral fl1) (EFloatLiteral fl2) = True
  easyMatch (ESetLiteral sl1) (ESetLiteral sl2) = True
  easyMatch (ESetComp sc1) (ESetComp sc2) = True
  easyMatch (EArrayLiteral al1) (EArrayLiteral al2) = True
  easyMatch (EArrayComp ac1) (EArrayComp ac2) = True
  easyMatch (EIfThenElseExpr itee1) (EIfThenElseExpr itee2) = True
  easyMatch (ELetExpr le1) (ELetExpr le2) = True
  easyMatch (ECallExpr ce1) (ECallExpr ce2) = True
  easyMatch (EGenCallExpr gce1) (EGenCallExpr gce2) = True
  easyMatch _ _ = False

instance EasyMatch ExprAtomTail where
  easyMatch EATNothing EATNothing = True
  easyMatch (ExprAtomTail _ _) (ExprAtomTail _ _) = True
  easyMatch _ _ = False

{-
instance EasyMatch SetLiteral where
  easyMatch (SetLiteral es1) (SetLiteral es2) =
    easyMatchLists es1 es2

instance EasyMatch SetComp where
  easyMatch (SetComp e1 ct1) (SetComp e2 ct2) =
    let locs1 = ctToLocalDecls ct1 ++ locs
        locs2 = ctToLocalDecls ct2 ++ locs1
    in easyMatch e1 e22 && easyMatch ct1 ct22

instance EasyMatch CompTail where
  easyMatch (CompTail gs1 Nothing) (CompTail gs2 Nothing) =
    easyMatchLists gs1 gs2
  easyMatch (CompTail _ Nothing) _ _ _ = False
  easyMatch _ (CompTail _ Nothing) _ _ = False
  easyMatch (CompTail gs1 (Just e1)) (CompTail gs2 (Just e2)) =
    easyMatch e1 e2 && easyMatchLists gs1 gs2

instance EasyMatch Generator where
  easyMatch (Generator is1 e1) (Generator is2 e2) =
    is1 == is2 && easyMatch e1 e2 -- TODO: is is1 == is2 correct?

instance EasyMatch ArrayLiteral where
  easyMatch (ArrayLiteral es1) (ArrayLiteral es2) =
    and $ map (\(a,b) -> easyMatch a b) $ zip es1 es2

instance EasyMatch ArrayComp where
  easyMatch (ArrayComp e1 ct1) (ArrayComp e2 ct2) =
    let locs1 = ctToLocalDecls ct1 ++ locs
        locs2 = ctToLocalDecls ct2 ++ locs1
    in easyMatch e1 e22 && easyMatch ct1 ct22

instance EasyMatch ArrayAccessTail where
  easyMatch (ArrayAccessTail es1) (ArrayAccessTail es2) =
    and $ map (\(a,b) -> easyMatch a b) $ zip es1 es2

instance EasyMatch IfThenElseExpr where
  easyMatch (IfThenElseExpr c1 e1 ces1 ee1) (IfThenElseExpr c2 e2 ces2 ee2) =
    easyMatch c1 c2 && easyMatch e1 e2 &&
    easyMatchTupleLists ces1 ces2 && easyMatch ee1 ee2 -- TODO easyMatchListsTuples?

instance EasyMatch CallExpr where
  easyMatch (CallExpr ioqo1 es1) (CallExpr ioqo2 es2) =
    ioqo1 == ioqo2 && easyMatchLists es1 es2

instance EasyMatch LetExpr where
  easyMatch (LetExpr lis1 e1) (LetExpr lis2 e2) =
    let locs1 = lisToLocalDecls lis1 ++ locs
        locs2 = lisToLocalDecls lis2 ++ locs1
    in easyMatch e1 e22 && easyMatchLists lis1 lis22

instance EasyMatch LetItem where
  easyMatch (LConstraintItem ci1) (LConstraintItem ci2) =
    easyMatch ci1 ci2
  easyMatch (LVarDeclItem vdi1) (LVarDeclItem vdi2) =
    easyMatch vdi1 vdi2
  easyMatch _ _ = False

instance EasyMatch GenCallExpr where
  easyMatch (GenCallExpr i1 ct1 e1) (GenCallExpr i2 ct2 e2) =
    let locs1 = ctToLocalDecls ct1 ++ locs
        locs2 = ctToLocalDecls ct2 ++ locs1
    in i1 == i2 && easyMatch ct1 ct22 && easyMatch e1 e22

instance EasyMatch Ident where
  easyMatch i1 i2 =
    let bte1 = case findDecl env1 i1 of
                 Just (Declaration bte _) -> bte
                 Nothing -> error
                            ("Error! Declaration for `" ++ show i1 ++
                             "' not found easyMatch." ++
                             "\nWith: " ++ show env)
        bte2 = case findDecl env1 i2 of
                 Just (Declaration bte _) -> bte
                 Nothing -> error
                            ("Error! Declaration for `" ++ show i2 ++
                             "' not found in easyMatch." ++
                             "\nWith Env: " ++ show env)
    in {-trace ("bte1: " ++ show bte1 ++ ", bte2: " ++ show bte2)-} bte1 == bte2
    where env1 = foldl (\env decl -> insertDeclaration decl env)
--    mSameType (findDecl env i1) (findDecl env i2)

instance EasyMatch IdentOrQuotedOp where
  easyMatch (IIdent i1) (IIdent i2) = easyMatch i1 i2
-}
