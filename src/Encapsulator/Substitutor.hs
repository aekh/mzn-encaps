{-| Substitutor -}

module Encapsulator.Substitutor where

import Data.Maybe
import Data.List (sortBy, zip3)

import FMD
import {- qualified -} CST
import qualified CST.Utils as CST
--import Encapsulator.Extractor
import Encapsulator.Common
--import Encapsulator.Ranker

import Debug.Trace

printy [] _ _ = []
printy ((e,_):xs) fmd heur = (e, heur e fmd []) : printy xs fmd heur

pruneStupids :: [(Vertex, a)] -> [(Vertex, a)]
pruneStupids vs = filter f vs
  where f (Vertex
           (Expr
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
                        (ExprAtom
                         (ECallExpr
                          (CallExpr (IIdent i) _)) _ _)))))))))))))),_) =
          isNothing $ findDef baseEnv i
        f _ = True

substitute :: FMD -> Int -> Heurs Vertex -> Attitude -> (FMD, CST.PredicateItem)
substitute fmd@(FMD env vs es) rank ranker att =
  let list = sort att $ ranker vs fmd
      (_, vId) = list !! rank
      (Vertex oldExpr) = vs !! vId
      (defn, predName) = predicateDef oldExpr env
      newExpr = predicateCall oldExpr env predName
      fmd1 = FMD env (replaceNth vId (Vertex newExpr) vs) es
      parents = filter (\(Edge _ _ to) -> to == vId) es
      queue = zip3 parents (repeat oldExpr) (repeat newExpr)
  in (substitute' fmd1 queue, defn)

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
  | n == 0 = newVal:xs
  | otherwise = x:replaceNth (n-1) newVal xs

substitute' :: FMD -> [(Edge, CST.Expr, CST.Expr)] -> FMD
substitute' fmd [] = fmd
substitute'
  (FMD env vs es) ((Edge Subformula vId _, oldPart, newPart):xs) =
  let (Vertex oldExpr) = vs !! vId
      newExpr' = substitutePart oldExpr oldPart newPart env
      newExpr = revertConvs newExpr' env
      fmd1 = FMD env (replaceNth vId (Vertex newExpr) vs) es
      parents = filter (\(Edge _ _ to) -> to == vId) es
      queue = zip3 parents (repeat oldExpr) (repeat newExpr)
  in substitute' fmd1 $ xs ++ queue
substitute'
  (FMD env vs es) ((Edge Abstraction vId _, abstr, predicateCall):xs) =
  let Vertex parent = vs !! vId
      pairs = mismatchPairs abstr parent
      newExpr = foldl f predicateCall pairs
      fmd1 = FMD env (replaceNth vId (Vertex newExpr) vs) es
      parents = filter (\(Edge _ _ to) -> to == vId) es
      queue = zip3 parents (repeat parent) (repeat newExpr)
  in substitute' fmd1 $ xs ++ queue
  where f :: Expr -> (Expr, Expr) -> Expr
        f e (oldPart, newPart) = substitutePart e oldPart newPart env

predicateCall :: CST.Expr -> Environment -> CST.Ident -> CST.Expr
predicateCall e env predId =
  let args = CST.identifiers e
  in expratom (CST.ExprAtom
               (CST.ECallExpr
                 (CST.CallExpr (CST.IIdent predId) (map identToExpr args)))
               CST.EATNothing
               (CST.Annotations []))

identToExpr :: CST.Ident -> CST.Expr
identToExpr i = expratom (CST.ExprAtom
                          (CST.EIdentOrQuotedOp (CST.IIdent i))
                          CST.EATNothing
                          (CST.Annotations []))

predicateDef :: CST.Expr -> Environment -> (CST.PredicateItem, CST.Ident)
predicateDef e env =
  let args = CST.identifiers e
      teais = mapMaybe (`identToTiExprAndId` env) args
      predId = CST.Ident "PREDICATE_0"
  in (CST.PredicateItem (CST.OperationItemTail
                         predId
                         (CST.Params teais)
                         presolveAnn
                         (Just e))
     ,predId)

identToTiExprAndId :: CST.Ident -> Environment -> Maybe CST.TiExprAndId
identToTiExprAndId i env =
  case findDecl env i of
    Just (Declaration bte _) -> Just $ CST.TiExprAndId (CST.TiExpr bte) i
    Nothing -> Nothing

expratom :: CST.ExprAtom -> CST.Expr
expratom ea =
  CST.Expr
  (CST.EExpr11
   (CST.EExpr10
    (CST.EExpr9
     (CST.EExpr8
      (CST.EExpr7
       (CST.EExpr6
        (CST.EExpr5
         (CST.EExpr4
          (CST.EExpr3 (CST.EExpr2 (CST.EExpr1 (CST.EExprAtom ea))))))))))))

presolveAnn :: CST.Annotations
presolveAnn =
  let autotable = expratom (CST.ExprAtom
                             (CST.EIdentOrQuotedOp
                               (CST.IIdent (CST.Ident "autotable")))
                            CST.EATNothing
                            (CST.Annotations []))
      presolve = CST.ECallExpr
                 (CST.CallExpr
                   (CST.IIdent (CST.Ident "presolve")) [autotable])
  in CST.Annotations [CST.Annotation presolve CST.EATNothing]


---------------------
-- SUBSTITUTE PART --
---------------------

revertAbstrs :: (Identifiers a, SubstitutePart a) => a -> Environment -> a
revertAbstrs e env =
  let froms = identifiers e
      olds = filter (\x -> case findExpr env x of
                             Just y -> True
                             Nothing -> False) froms
      news = map (\i -> case findExpr env i of Just e -> e) olds
  in f e olds news
  where f :: SubstitutePart a => a -> [Ident] -> [Expr] -> a
        f e [] [] = e
        f e (o:olds) (n:news) =
          f (substitutePart e (CST.toExpr o) n env) olds news

revertConvs :: (RevertConversions a, Identifiers a) => a -> Environment -> a
revertConvs e env =
  let olds = identifiers e
      table = map (\old -> case findOrig env old of Just new -> (old,new))
                $ filter (\x -> case findOrig env x of
                                  Just y -> True
                                  Nothing -> False) olds
  in revertConversions e table []

class SubstitutePart x where
  substitutePart :: x -> CST.Expr -> CST.Expr -> Environment -> x
  replace :: x -> CST.Expr -> x
  mismatchPairs :: x -> x -> [(CST.Expr, CST.Expr)]

instance SubstitutePart TiExprAndId where
  substitutePart (TiExprAndId (TiExpr bte) i) old new env =
    TiExprAndId (TiExpr $ substitutePart bte old new env) i
  replace = undefined
  mismatchPairs (TiExprAndId (TiExpr bte1) i1) (TiExprAndId (TiExpr bte2) i2)
    | i1 == i2 = mismatchPairs bte1 bte2
  mismatchPairs _ _ = error "Impossible mismatch (VarDeclItem)"

instance SubstitutePart VarDeclItem where
  substitutePart (VarDeclItem teai as mE) old new env =
    VarDeclItem
    (substitutePart teai old new env)
    as -- implement on annotations?
    ((\x -> substitutePart x old new env) <$> mE )
  replace = undefined
  mismatchPairs (VarDeclItem teai1 _ Nothing)
                (VarDeclItem teai2 _ Nothing) =
    mismatchPairs teai1 teai2
  mismatchPairs (VarDeclItem teai1 _ (Just e1))
                (VarDeclItem teai2 _ (Just e2)) =
    mismatchPairs teai1 teai2 ++
    mismatchPairs e1 e2
  mismatchPairs _ _ = error "Impossible mismatch (VarDeclItem)"

instance SubstitutePart ConstraintItem where
  substitutePart (ConstraintItem e) old new env =
    ConstraintItem $ substitutePart e old new env
  replace = undefined
  mismatchPairs (ConstraintItem e1) (ConstraintItem e2) =
    mismatchPairs e1 e2

instance SubstitutePart TiExpr where
  substitutePart (TiExpr bte) old new env =
    TiExpr $ substitutePart bte old new env
  mismatchPairs (TiExpr bte1) (TiExpr bte2) =
    mismatchPairs bte1 bte2

instance SubstitutePart BaseTiExpr where
  substitutePart (BaseTiExpr vp btet) old new env =
    BaseTiExpr vp $ substitutePart btet old new env
  replace = undefined
  mismatchPairs (BaseTiExpr vp1 btet1) (BaseTiExpr vp2 btet2)
    | vp1 == vp2 = mismatchPairs btet1 btet2
  mismatchPairs _ _ = error "Impossible mismatch (BaseTiExpr)"

instance SubstitutePart BaseTiExprTail where
  substitutePart (BIdent i) old new env =
    BIdent $ substitutePart i old new env
  substitutePart (BSetTiExprTail stet) old new env =
    error "substitutePart on BSetTiExprTail not implemented!"
    -- BSetTiExprTail$ substitutePart stet old new env
  substitutePart (BArrayTiExprTail atet) old new env =
    BArrayTiExprTail $ substitutePart atet old new env
  substitutePart (BSet es) old new env =
    BSet $ map (\x -> substitutePart x old new env) es
  substitutePart (BRange ne1 ne2) old new env =
    BRange (substitutePart ne1 old new env) (substitutePart ne2 old new env)
  substitutePart (BExpr6 e) old new env =
    BExpr6 $ substitutePart e old new env
  substitutePart btet _ _ _ = btet
  replace = undefined
  mismatchPairs (BIdent i1) (BIdent i2)
    | i1 == i2 = []
    | otherwise = [(CST.toExpr i1, CST.toExpr i2)]
  mismatchPairs BBool BBool = []
  mismatchPairs BInt BInt = []
  mismatchPairs BFloat BFloat = []
  mismatchPairs (BSetTiExprTail stet1) (BSetTiExprTail stet2) =
    mismatchPairs stet1 stet2
  mismatchPairs (BArrayTiExprTail atet1) (BArrayTiExprTail atet2) =
    mismatchPairs atet1 atet2
  mismatchPairs (BSet es1) (BSet es2)
    | length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y
  mismatchPairs (BRange ne11 ne12) (BRange ne21 ne22) =
    mismatchPairs ne11 ne21 ++
    mismatchPairs ne12 ne22
  mismatchPairs (BExpr6 e1) (BExpr6 e2) =
    mismatchPairs e1 e2
  mismatchPairs _ _ = error "Impossible mismatch (BaseTiExprTail)"

instance SubstitutePart SetTiExprTail where
  mismatchPairs SInt SInt = []
  mismatchPairs (SSet es1) (SSet es2)
    | length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y
  mismatchPairs (SRange ne11 ne12) (SRange ne21 ne22) =
    mismatchPairs ne11 ne21 ++
    mismatchPairs ne12 ne22
  mismatchPairs (SExpr6 e1) (SExpr6 e2) =
    mismatchPairs e1 e2

instance SubstitutePart ArrayTiExprTail where
  substitutePart (ArrayTiExprTail tes te) old new env =
    ArrayTiExprTail tes1 $ substitutePart te old new env
    where tes1 = map (\x -> substitutePart x old new env) tes
  mismatchPairs (ArrayTiExprTail tes1 te1) (ArrayTiExprTail tes2 te2)
    | length tes1 == length tes2 =
        mismatchPairs te1 te2 ++
        concatMap f (zip tes1 tes2)
    where f (x,y) = mismatchPairs x y

instance SubstitutePart Expr where
  substitutePart expr@(Expr e) old new env =
    let isMatch = equiv expr old env
    in if isMatch
         then new
         else Expr $ substitutePart e old new env
  replace = undefined
  mismatchPairs (Expr e1) (Expr e2) =
    mismatchPairs e1 e2

instance SubstitutePart Expr12 where
  substitutePart e@(EEquivalence e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EEquivalence
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr11 e) old new env =
    EExpr11 $ substitutePart e old new env
  replace _ (Expr e) = e
  mismatchPairs (EExpr11 e1) (EExpr11 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EEquivalence e11 e12) (EEquivalence e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr11 where
  substitutePart e@(ERImplies e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ERImplies
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ELImplies e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ELImplies
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr10 e) old new env =
    EExpr10 $ substitutePart e old new env
  replace _ (Expr (EExpr11 e)) = e
  mismatchPairs (EExpr10 e1) (EExpr10 e2) =
    mismatchPairs e1 e2
  mismatchPairs (ERImplies e11 e12) (ERImplies e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr10 where
  substitutePart e@(EOr e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EOr
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EXor e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EXor
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr9 e) old new env =
    EExpr9 $ substitutePart e old new env
  replace _ (Expr (EExpr11 (EExpr10 e))) = e
  mismatchPairs (EExpr9 e1) (EExpr9 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EOr e11 e12) (EOr e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EXor e11 e12) (EXor e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr9 where
  substitutePart e@(EAnd e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EAnd
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr8 e) old new env =
    EExpr8 $ substitutePart e old new env
  replace _ (Expr (EExpr11 (EExpr10 (EExpr9 e)))) = e
  mismatchPairs (EExpr8 e1) (EExpr8 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EAnd e11 e12) (EAnd e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr8 where
  substitutePart e@(ELt e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ELt
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EGt e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EGt
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ELeq e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ELeq
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EGeq e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EGeq
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EEqEq e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EEqEq
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EEq e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EEq
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ENeq e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ENeq
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr7 e) old new env =
    EExpr7 $ substitutePart e old new env
  replace _ (Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 e))))) = e
  mismatchPairs (EExpr7 e1) (EExpr7 e2) =
    mismatchPairs e1 e2
  mismatchPairs (ELt e11 e12) (ELt e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EGt e11 e12) (EGt e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ELeq e11 e12) (ELeq e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EGeq e11 e12) (EGeq e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EEq e11 e12) (EEq e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EEqEq e11 e12) (EEqEq e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ENeq e11 e12) (ENeq e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr7 where
  substitutePart e@(EIn e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EIn
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ESubset e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ESubset
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ESuperset e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ESuperset
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr6 e) old new env =
    EExpr6 $ substitutePart e old new env
  replace _ (Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 e)))))) = e
  mismatchPairs (EExpr6 e1) (EExpr6 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EIn e11 e12) (EIn e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ESubset e11 e12) (ESubset e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ESuperset e11 e12) (ESuperset e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr6 where
  substitutePart e@(EUnion e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EUnion
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EDiff e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EDiff
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ESymDiff e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ESymDiff
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr5 e) old new env =
    EExpr5 $ substitutePart e old new env
  replace _ (Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 e))))))) = e
  mismatchPairs (EExpr5 e1) (EExpr5 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EUnion e11 e12) (EUnion e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EDiff e11 e12) (EDiff e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ESymDiff e11 e12) (ESymDiff e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr5 where
  substitutePart e@(EEllipsis e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EEllipsis
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr4 e) old new env =
    EExpr4 $ substitutePart e old new env
  replace _ (Expr
             (EExpr11
              (EExpr10
               (EExpr9
                (EExpr8
                 (EExpr7
                  (EExpr6
                   (EExpr5 e)))))))) = e
  mismatchPairs (EExpr4 e1) (EExpr4 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EEllipsis e11 e12) (EEllipsis e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr4 where
  substitutePart e@(EPlus e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EPlus
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EMinus e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EMinus
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr3 e) old new env =
    EExpr3 $ substitutePart e old new env
  replace _ (Expr
             (EExpr11
              (EExpr10
               (EExpr9
                (EExpr8
                 (EExpr7
                  (EExpr6
                   (EExpr5
                    (EExpr4 e))))))))) = e
  mismatchPairs (EExpr3 e1) (EExpr3 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EPlus e11 e12) (EPlus e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EMinus e11 e12) (EMinus e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr3 where
  substitutePart e@(EStar e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EStar
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EDiv e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EDiv
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EMod e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EMod
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(ESlash e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else ESlash
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart e@(EIntersect e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EIntersect
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr2 e) old new env =
    EExpr2 $ substitutePart e old new env
  replace _ (Expr
             (EExpr11
              (EExpr10
               (EExpr9
                (EExpr8
                 (EExpr7
                  (EExpr6
                   (EExpr5
                    (EExpr4
                     (EExpr3 e)))))))))) = e
  mismatchPairs (EExpr2 e1) (EExpr2 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EStar e11 e12) (EStar e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EDiv e11 e12) (EDiv e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EMod e11 e12) (EMod e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (ESlash e11 e12) (ESlash e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (EIntersect e11 e12) (EIntersect e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr2 where
  substitutePart e@(EPlusPlus e1 e2) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EPlusPlus
              (substitutePart e1 old new env)
              (substitutePart e2 old new env)
  substitutePart (EExpr1 e) old new env =
    EExpr1 $ substitutePart e old new env
  replace _ (Expr
             (EExpr11
              (EExpr10
               (EExpr9
                (EExpr8
                 (EExpr7
                  (EExpr6
                   (EExpr5
                    (EExpr4
                     (EExpr3
                      (EExpr2 e))))))))))) = e
  mismatchPairs (EExpr1 e1) (EExpr1 e2) =
    mismatchPairs e1 e2
  mismatchPairs (EPlusPlus e11 e12) (EPlusPlus e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart Expr1 where
  substitutePart e@(EIdent i e1 ea) old new env =
    let expr = CST.toExpr e
    in if equiv expr old env
         then replace e new
         else EIdent
              (substitutePart i old new env)
              (substitutePart e1 old new env)
              (substitutePart ea old new env)
  substitutePart (EExprAtom ea) old new env =
    EExprAtom $ substitutePart ea old new env
  replace _ (Expr
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
                       (EExpr1 e)))))))))))) = e
  mismatchPairs (EExprAtom e1) (EExprAtom e2) =
    mismatchPairs e1 e2
  mismatchPairs (EIdent i1 e11 e12) (EIdent i2 e21 e22)
    | i1 == i2 =
        mismatchPairs e11 e21 ++
        mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart ExprAtom where
  substitutePart (ExprAtom eah eat as) old new env =
    ExprAtom
    (substitutePart eah old new env)
    (substitutePart eat old new env)
    as -- skip annotations ?
  replace _ (Expr
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
                         ea))))))))))))) = ea
  mismatchPairs (ExprAtom eah1 EATNothing _) (ExprAtom eah2 EATNothing _) =
    mismatchPairs eah1 eah2
  mismatchPairs ee1@(ExprAtom _ EATNothing _) ee2@ExprAtom{} =
    [(CST.toExpr ee1, CST.toExpr ee2)]
  mismatchPairs (ExprAtom eah1 eat1 _) (ExprAtom eah2 eat2 _) =
    mismatchPairs eah1 eah2 ++
    mismatchPairs eat1 eat2
  --mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart ExprAtomHead where
  substitutePart eah@(EBuiltinUnOp buo ea) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EBuiltinUnOp buo $ substitutePart ea old new env
  substitutePart eah@(EExpr e) old new env =
    {-let expr = CST.toExpr eah env
        equiv expr old env = length forms == 1 && equiv (head forms) old env
    in if equiv expr old env
         then traceShow new $ replace eah new
         else-} EExpr $ substitutePart e old new env
  substitutePart eah@(EIdentOrQuotedOp ioqo) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EIdentOrQuotedOp $ substitutePart ioqo old new env
  substitutePart x@(EBoolLiteral _) _ _ _ = x
  substitutePart x@(EIntLiteral _) _ _ _ = x
  substitutePart x@(EFloatLiteral _) _ _ _ = x
  substitutePart eah@(ESetLiteral sl) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else ESetLiteral $ substitutePart sl old new env
  substitutePart eah@(ESetComp sc) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else ESetComp $ substitutePart sc old new env
  substitutePart eah@(EArrayLiteral al) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EArrayLiteral $ substitutePart al old new env
  substitutePart eah@(EArrayComp ac) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EArrayComp $ substitutePart ac old new env
  substitutePart eah@(EIfThenElseExpr itee) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EIfThenElseExpr $ substitutePart itee old new env
  substitutePart eah@(ELetExpr le) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else ELetExpr $ substitutePart le old new env
  substitutePart eah@(ECallExpr ce) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else ECallExpr $ substitutePart ce old new env
  substitutePart eah@(EGenCallExpr gce) old new env =
    let expr = CST.toExpr eah
    in if equiv expr old env
         then replace eah new
         else EGenCallExpr $ substitutePart gce old new env
  replace _ (Expr
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
                         (ExprAtom
                          eah
                          EATNothing
                          (Annotations []))))))))))))))) = eah
  mismatchPairs (EBuiltinUnOp buo1 ea1) (EBuiltinUnOp buo2 ea2)
    | buo1 == buo2 = mismatchPairs ea1 ea2
  mismatchPairs (EExpr e1) (EExpr e2) =
    mismatchPairs e1 e2
  mismatchPairs (EIdentOrQuotedOp ioqo1) (EIdentOrQuotedOp ioqo2) =
    mismatchPairs ioqo1 ioqo2
  mismatchPairs (EBoolLiteral bl1) (EBoolLiteral bl2)
    | bl1 == bl2 = []
  mismatchPairs (EIntLiteral il1) (EIntLiteral il2)
    | il1 == il2 = []
  mismatchPairs (EFloatLiteral fl1) (EFloatLiteral fl2)
    | fl1 == fl2 = []
  mismatchPairs (ESetLiteral sl1) (ESetLiteral sl2) =
    mismatchPairs sl1 sl2
  mismatchPairs (ESetComp sc1) (ESetComp sc2) =
    mismatchPairs sc1 sc2
  mismatchPairs (EArrayLiteral al1) (EArrayLiteral al2) =
    mismatchPairs al1 al2
  mismatchPairs (EArrayComp ac1) (EArrayComp ac2) =
    mismatchPairs ac1 ac2
  mismatchPairs (EIfThenElseExpr itee1) (EIfThenElseExpr itee2) =
    mismatchPairs itee1 itee2
  mismatchPairs (ELetExpr le1) (ELetExpr le2) =
    mismatchPairs le1 le2
  mismatchPairs (ECallExpr ce1) (ECallExpr ce2) =
    mismatchPairs ce1 ce2
  mismatchPairs (EGenCallExpr gce1) (EGenCallExpr gce2) =
    mismatchPairs gce1 gce2
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart ExprAtomTail where
  substitutePart (ExprAtomTail aat eat) old new env =
    ExprAtomTail (substitutePart aat old new env) (substitutePart eat old new env)
  substitutePart EATNothing _ _ _ = EATNothing
  replace = undefined
  mismatchPairs (ExprAtomTail aat1 eat1) (ExprAtomTail aat2 eat2) =
    mismatchPairs aat1 aat2 ++
    mismatchPairs eat1 eat2
  mismatchPairs EATNothing EATNothing = []
  mismatchPairs _ _ = error "Impossible mismatch (ExprAtomTail)"

instance SubstitutePart NumExpr where
  substitutePart (NumExpr e) old new env =
    NumExpr $ substitutePart e old new env
  replace = undefined
  mismatchPairs (NumExpr e1) (NumExpr e2) =
    mismatchPairs e1 e2

instance SubstitutePart NumExpr4 where
  substitutePart (NPlus e1 e2) old new env =
    NPlus (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NMinus e1 e2) old new env =
    NMinus (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NNumExpr3 e) old new env =
    NNumExpr3 $ substitutePart e old new env
  replace = undefined
  mismatchPairs (NNumExpr3 e1) (NNumExpr3 e2) =
    mismatchPairs e1 e2
  mismatchPairs (NPlus e11 e12) (NPlus e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (NMinus e11 e12) (NMinus e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart NumExpr3 where
  substitutePart (NStar e1 e2) old new env =
    NStar (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NDiv e1 e2) old new env =
    NDiv (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NMod e1 e2) old new env =
    NMod (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NSlash e1 e2) old new env =
    NSlash (substitutePart e1 old new env) (substitutePart e2 old new env)
  substitutePart (NNumExpr1 e) old new env =
    NNumExpr1 $ substitutePart e old new env
  replace = undefined
  mismatchPairs (NNumExpr1 e1) (NNumExpr1 e2) =
    mismatchPairs e1 e2
  mismatchPairs (NStar e11 e12) (NStar e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (NDiv e11 e12) (NDiv e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (NMod e11 e12) (NMod e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs (NSlash e11 e12) (NSlash e21 e22) =
    mismatchPairs e11 e21 ++
    mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart NumExpr1 where
  substitutePart (NIdent i e1 ea) old new env =
    NIdent
    (substitutePart i old new env)
    (substitutePart e1 old new env)
    (substitutePart ea old new env)
  substitutePart (NNumExprAtom ea) old new env =
    NNumExprAtom $ substitutePart ea old new env
  replace = undefined
  mismatchPairs (NNumExprAtom e1) (NNumExprAtom e2) =
    mismatchPairs e1 e2
  mismatchPairs (NIdent i1 e11 e12) (NIdent i2 e21 e22)
    | i1 == i2 =
        mismatchPairs e11 e21 ++
        mismatchPairs e12 e22
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart NumExprAtom where
  substitutePart (NumExprAtom eah eat as) old new env =
    NumExprAtom
    (substitutePart eah old new env)
    (substitutePart eat old new env)
    as -- fix annotations?
  replace = undefined
  mismatchPairs (NumExprAtom eah1 eat1 _) (NumExprAtom eah2 eat2 _) =
    mismatchPairs eah1 eah2 ++
    mismatchPairs eat1 eat2

instance SubstitutePart NumExprAtomHead where
  substitutePart (NBuiltinNumUnOp buo ea) old new env =
    NBuiltinNumUnOp buo $ substitutePart ea old new env
  substitutePart (NNumExpr e) old new env =
    NNumExpr $ substitutePart e old new env
  substitutePart (NIdentOrQuotedOp ioqo) old new env =
    NIdentOrQuotedOp $ substitutePart ioqo old new env
  substitutePart x@(NIntLiteral _) _ _ _ = x
  substitutePart x@(NFloatLiteral _) _ _ _ = x
  substitutePart (NIfThenElseExpr itee) old new env =
    NIfThenElseExpr $ substitutePart itee old new env
  substitutePart (NLetExpr le) old new env =
    NLetExpr $ substitutePart le old new env
  substitutePart (NCallExpr ce) old new env =
    NCallExpr $ substitutePart ce old new env
  substitutePart (NGenCallExpr gce) old new env =
    NGenCallExpr $ substitutePart gce old new env
  replace = undefined
  mismatchPairs (NBuiltinNumUnOp buo1 ea1) (NBuiltinNumUnOp buo2 ea2)
    | buo1 == buo2 = mismatchPairs ea1 ea2
  mismatchPairs (NNumExpr e1) (NNumExpr e2) =
    mismatchPairs e1 e2
  mismatchPairs (NIdentOrQuotedOp ioqo1) (NIdentOrQuotedOp ioqo2) =
    mismatchPairs ioqo1 ioqo2
  mismatchPairs (NIntLiteral il1) (NIntLiteral il2)
    | il1 == il2 = []
  mismatchPairs (NFloatLiteral fl1) (NFloatLiteral fl2)
    | fl1 == fl2 = []
  mismatchPairs (NIfThenElseExpr itee1) (NIfThenElseExpr itee2) =
    mismatchPairs itee1 itee2
  mismatchPairs (NLetExpr le1) (NLetExpr le2) =
    mismatchPairs le1 le2
  mismatchPairs (NCallExpr ce1) (NCallExpr ce2) =
    mismatchPairs ce1 ce2
  mismatchPairs (NGenCallExpr gce1) (NGenCallExpr gce2) =
    mismatchPairs gce1 gce2
  mismatchPairs e1 e2 = [(CST.toExpr e1, CST.toExpr e2)]

instance SubstitutePart SetLiteral where
  substitutePart sl@(SetLiteral es) old new env =
    let expr = CST.toExpr sl
    in if equiv expr old env
         then replace sl new
         else SetLiteral $ map (\x -> substitutePart x old new env) es
  replace _ (Expr
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
                         (ExprAtom
                          (ESetLiteral sl)
                          EATNothing
                          (Annotations []))))))))))))))) = sl
  mismatchPairs (SetLiteral es1) (SetLiteral es2)
    | length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart SetComp where
  substitutePart sc@(SetComp e ct) old new env =
    let expr = CST.toExpr sc
    in if equiv expr old env
         then replace sc new
         else SetComp
              (substitutePart e old new env) -- update env w/ locals?
              (substitutePart ct old new env)
  replace _ (Expr
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
                         (ExprAtom
                          (ESetComp sc)
                          EATNothing
                          (Annotations []))))))))))))))) = sc
  mismatchPairs (SetComp e1 ct1) (SetComp e2 ct2) =
    mismatchPairs e1 e2 ++
    mismatchPairs ct1 ct2

instance SubstitutePart CompTail where
  substitutePart (CompTail gs Nothing) old new env =
    CompTail (map (\x -> substitutePart x old new env) gs) Nothing
  substitutePart (CompTail gs (Just e)) old new env =
    CompTail
    (map (\x -> substitutePart x old new env) gs)
    (Just (substitutePart e old new env))
  replace = undefined
  mismatchPairs (CompTail gs1 Nothing) (CompTail gs2 Nothing)
    | length gs1 == length gs2 =
        concatMap f $ zip gs1 gs2
    where f (x,y) = mismatchPairs x y
  mismatchPairs (CompTail gs1 (Just e1)) (CompTail gs2 (Just e2))
    | length gs1 == length gs2 =
        concatMap f (zip gs1 gs2) ++
        mismatchPairs e1 e2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart Generator where
  substitutePart (Generator is e) old new env =
    Generator is (substitutePart e old new env)
  replace = undefined
  mismatchPairs (Generator is1 e1) (Generator is2 e2)
    | length is1 == length is2 =
        concatMap f (zip is1 is2) ++
        mismatchPairs e1 e2
    where f (x,y) = mismatchPairs x y
  mismatchPairs _ _ = error "Impossible mismatch (Generator)"

instance SubstitutePart ArrayLiteral where
  substitutePart al@(ArrayLiteral es) old new env =
    let expr = CST.toExpr al
    in if equiv expr old env
         then replace al new
         else ArrayLiteral $ map (\x -> substitutePart x old new env) es
  replace _ (Expr
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
                         (ExprAtom
                          (EArrayLiteral al)
                          EATNothing
                          (Annotations []))))))))))))))) = al
  mismatchPairs (ArrayLiteral es1) (ArrayLiteral es2)
    | length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart ArrayComp where
  substitutePart ac@(ArrayComp e ct) old new env =
    let expr = CST.toExpr ac
    in if equiv expr old env
         then replace ac new
         else ArrayComp
              (substitutePart e old new env) -- update env w/ locals?
              (substitutePart ct old new env)
  replace _ (Expr
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
                         (ExprAtom
                          (EArrayComp ac)
                          EATNothing
                          (Annotations []))))))))))))))) = ac
  mismatchPairs (ArrayComp e1 ct1) (ArrayComp e2 ct2) =
    mismatchPairs e1 e2 ++
    mismatchPairs ct1 ct2

instance SubstitutePart ArrayAccessTail where
  substitutePart (ArrayAccessTail es) old new env =
    ArrayAccessTail $ map (\x -> substitutePart x old new env) es
  replace = undefined
  mismatchPairs (ArrayAccessTail es1) (ArrayAccessTail es2)
    | length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart IfThenElseExpr where
  substitutePart itee@(IfThenElseExpr c e ces ee) old new env =
    let expr = CST.toExpr itee
    in if equiv expr old env
         then replace itee new
         else IfThenElseExpr
              (substitutePart c old new env)
              (substitutePart e old new env)
              cesSubstituteParts
              (substitutePart ee old new env)
    where cesSubstituteParts =
            map
            (\(c,e) ->
               (substitutePart c old new env, substitutePart e old new env))
            ces
  replace _ (Expr
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
                         (ExprAtom
                          (EIfThenElseExpr itee)
                          EATNothing
                          (Annotations []))))))))))))))) = itee
  mismatchPairs (IfThenElseExpr c1 e1 ces1 ee1)
                (IfThenElseExpr c2 e2 ces2 ee2)
    | length ces1 == length ces2 =
        mismatchPairs c1 c2 ++
        mismatchPairs e1 e2 ++
        concatMap f (zip ces1 ces2) ++
        mismatchPairs ee1 ee2
    where f ((c1,e1),(c2,e2)) = mismatchPairs c1 c2 ++
                                mismatchPairs e1 e2

instance SubstitutePart CallExpr where
  substitutePart ce@(CallExpr ioqo es) old new env =
    let expr = CST.toExpr ce
    in if equiv expr old env
         then replace ce new
         else CallExpr
              (substitutePart ioqo old new env)
              (map (\x -> substitutePart x old new env) es)
  replace _ (Expr
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
                         (ExprAtom
                          (ECallExpr ce)
                          EATNothing
                          (Annotations []))))))))))))))) = ce
  mismatchPairs (CallExpr ioqo1 es1) (CallExpr ioqo2 es2)
    | ioqo1 == ioqo2 && length es1 == length es2 =
        concatMap f $ zip es1 es2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart LetExpr where
  substitutePart le@(LetExpr lis e) old new env =
    let expr = CST.toExpr le
    in if equiv expr old env
         then replace le new
         else LetExpr
              (map (\x -> substitutePart x old new env) lis)
              (substitutePart e old new env) -- update env w/ locals?
  replace _ (Expr
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
                         (ExprAtom
                          (ELetExpr le)
                          EATNothing
                          (Annotations []))))))))))))))) = le
  mismatchPairs (LetExpr lis1 e1) (LetExpr lis2 e2)
    | length lis1 == length lis2 =
        concatMap f (zip lis1 lis2) ++
        mismatchPairs e1 e2
    where f (x,y) = mismatchPairs x y

instance SubstitutePart LetItem where
  substitutePart (LVarDeclItem vdi) old new env =
    LVarDeclItem $ substitutePart vdi old new env
  substitutePart (LConstraintItem ci) old new env =
    LConstraintItem $ substitutePart ci old new env
  replace = undefined
  mismatchPairs (LVarDeclItem vdi1) (LVarDeclItem vdi2) =
    mismatchPairs vdi1 vdi2
  mismatchPairs (LConstraintItem ci1) (LConstraintItem ci2) =
    mismatchPairs ci1 ci2
  mismatchPairs _ _ = error "Impossible mismatch (LetItem)"

instance SubstitutePart GenCallExpr where -- TODO: LOCALS!!
  substitutePart gce@(GenCallExpr ioqo ct e) old new env =
    let expr = CST.toExpr gce
    in if equiv expr old env
         then replace gce new
         else GenCallExpr
              (substitutePart ioqo old new env)
              (substitutePart ct old new env)
              (substitutePart e old new env) -- update env w/ locals?
  replace _ (Expr
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
                         (ExprAtom
                          (EGenCallExpr gce)
                          EATNothing
                          (Annotations []))))))))))))))) = gce
  mismatchPairs (GenCallExpr ioqo1 ct1 e1) (GenCallExpr ioqo2 ct2 e2)
    | ioqo1 == ioqo2 =
        mismatchPairs ct1 ct2 ++
        mismatchPairs e1 e2
  mismatchPairs _ _ = error "Impossible mismatch (GenCallExpr)"

instance SubstitutePart Ident where
  substitutePart i old new env =
    let expr = CST.toExpr i
    in if equiv expr old env
         then replace i new
         else i
  replace _ (Expr
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
                         (ExprAtom
                          (EIdentOrQuotedOp (IIdent i))
                          EATNothing
                          (Annotations []))))))))))))))) = i
  mismatchPairs (Ident i1) (Ident i2)
    | i1 == i2 = []
  mismatchPairs i1 i2 = [(CST.toExpr i1, CST.toExpr i2)]


instance SubstitutePart IdentOrQuotedOp where
  substitutePart ioqo@(IIdent i) old new env =
    let expr = CST.toExpr ioqo
    in if equiv expr old env
         then replace ioqo new
         else IIdent $ substitutePart i old new env
  replace _ (Expr
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
                         (ExprAtom
                          (EIdentOrQuotedOp i)
                          EATNothing
                          (Annotations []))))))))))))))) = i
  mismatchPairs (IIdent i1) (IIdent i2) =
    mismatchPairs i1 i2

--------------------------
-- REVERT CONVERSATIONS --
--------------------------

class RevertConversions x where
  revertConversions :: x -> [(Ident, Ident)] -> [Ident] -> x

instance RevertConversions TiExprAndId where
  revertConversions (TiExprAndId (TiExpr bte) i) table locs =
    TiExprAndId (TiExpr $ revertConversions bte table locs) i

instance RevertConversions VarDeclItem where
  revertConversions (VarDeclItem teai as mE) table locs =
    VarDeclItem
    (revertConversions teai table locs)
    (revertConversions as table locs)
    ((\x -> revertConversions x table locs) <$> mE )

instance RevertConversions ConstraintItem where
  revertConversions (ConstraintItem e) table locs =
    ConstraintItem $ revertConversions e table locs

instance RevertConversions BaseTiExpr where
  revertConversions (BaseTiExpr vp btet) table locs =
    BaseTiExpr vp $ revertConversions btet table locs

instance RevertConversions BaseTiExprTail where
  revertConversions (BIdent i) table locs =
    BIdent $ revertConversions i table locs
  revertConversions (BSetTiExprTail stet) table locs =
    error "revertConversions on BSetTiExprTail not implemented!"
    -- BSetTiExprTail$ revertConversions stet table locs
  revertConversions (BArrayTiExprTail atet) table locs =
    error "revertConversions on BArrayTiExprTail not implemented!"
    -- BArrayTiExprTail $ revertConversions atet table locs
  revertConversions (BSet es) table locs =
    BSet $ map (\x -> revertConversions x table locs) es
  revertConversions (BRange ne1 ne2) table locs =
    BRange (revertConversions ne1 table locs) (revertConversions ne2 table locs)
  revertConversions (BExpr6 e) table locs =
    BExpr6 $ revertConversions e table locs
  revertConversions btet _ _ = btet

instance RevertConversions Expr where
  revertConversions (Expr e) table locs = Expr $ revertConversions e table locs

instance RevertConversions Expr12 where
  revertConversions (EEquivalence e1 e2) table locs =
    EEquivalence (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr11 e) table locs = EExpr11 $ revertConversions e table locs

instance RevertConversions Expr11 where
  revertConversions (ERImplies e1 e2) table locs =
    ERImplies (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ELImplies e1 e2) table locs =
    ELImplies (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr10 e) table locs = EExpr10 $ revertConversions e table locs

instance RevertConversions Expr10 where
  revertConversions (EOr e1 e2) table locs =
    EOr (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EXor e1 e2) table locs =
    EXor (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr9 e) table locs = EExpr9 $ revertConversions e table locs

instance RevertConversions Expr9 where
  revertConversions (EAnd e1 e2) table locs =
    EAnd (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr8 e) table locs = EExpr8 $ revertConversions e table locs

instance RevertConversions Expr8 where
  revertConversions (ELt e1 e2) table locs =
    ELt (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EGt e1 e2) table locs =
    EGt (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ELeq e1 e2) table locs =
    ELeq (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EGeq e1 e2) table locs =
    EGeq (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EEqEq e1 e2) table locs =
    EEqEq (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EEq e1 e2) table locs =
    EEq (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ENeq e1 e2) table locs =
    ENeq (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr7 e) table locs = EExpr7 $ revertConversions e table locs

instance RevertConversions Expr7 where
  revertConversions (EIn e1 e2) table locs =
    EIn (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ESubset e1 e2) table locs =
    ESubset (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ESuperset e1 e2) table locs =
    ESuperset (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr6 e) table locs = EExpr6 $ revertConversions e table locs

instance RevertConversions Expr6 where
  revertConversions (EUnion e1 e2) table locs =
    EUnion (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EDiff e1 e2) table locs =
    EDiff (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ESymDiff e1 e2) table locs =
    ESymDiff (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr5 e) table locs = EExpr5 $ revertConversions e table locs

instance RevertConversions Expr5 where
  revertConversions (EEllipsis e1 e2) table locs =
    EEllipsis (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr4 e) table locs = EExpr4 $ revertConversions e table locs

instance RevertConversions Expr4 where
  revertConversions (EPlus e1 e2) table locs =
    EPlus (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EMinus e1 e2) table locs =
    EMinus (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr3 e) table locs = EExpr3 $ revertConversions e table locs

instance RevertConversions Expr3 where
  revertConversions (EStar e1 e2) table locs =
    EStar (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EDiv e1 e2) table locs =
    EDiv (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EMod e1 e2) table locs =
    EMod (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (ESlash e1 e2) table locs =
    ESlash (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EIntersect e1 e2) table locs =
    EIntersect (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr2 e) table locs = EExpr2 $ revertConversions e table locs

instance RevertConversions Expr2 where
  revertConversions (EPlusPlus e1 e2) table locs =
    EPlusPlus (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (EExpr1 e) table locs = EExpr1 $ revertConversions e table locs

instance RevertConversions Expr1 where
  revertConversions (EIdent i e1 ea) table locs =
    EIdent
    (revertConversions i table locs)
    (revertConversions e1 table locs)
    (revertConversions ea table locs)
  revertConversions (EExprAtom ea) table locs =
    EExprAtom $ revertConversions ea table locs

instance RevertConversions ExprAtom where
  revertConversions ea@(ExprAtom eah eat as) table locs =
    ExprAtom
    (revertConversions eah table locs)
    (revertConversions eat table locs)
    (revertConversions as table locs)

instance RevertConversions ExprAtomHead where
  revertConversions (EBuiltinUnOp buo ea) table locs =
    EBuiltinUnOp buo $ revertConversions ea table locs
  revertConversions (EExpr e) table locs =
    EExpr $ revertConversions e table locs
  revertConversions (EIdentOrQuotedOp ioqo) table locs =
    EIdentOrQuotedOp $ revertConversions ioqo table locs
  revertConversions x@(EBoolLiteral _) _ _ = x
  revertConversions x@(EIntLiteral _) _ _ = x
  revertConversions x@(EFloatLiteral _) _ _ = x
  revertConversions (ESetLiteral sl) table locs =
    ESetLiteral $ revertConversions sl table locs
  revertConversions (ESetComp sc) table locs =
    ESetComp $ revertConversions sc table locs
  revertConversions (EArrayLiteral al) table locs =
    EArrayLiteral $ revertConversions al table locs
  revertConversions (EArrayComp ac) table locs =
    EArrayComp $ revertConversions ac table locs
  revertConversions (EIfThenElseExpr itee) table locs =
    EIfThenElseExpr $ revertConversions itee table locs
  revertConversions (ELetExpr le) table locs =
    ELetExpr $ revertConversions le table locs
  revertConversions (ECallExpr ce) table locs =
    ECallExpr $ revertConversions ce table locs
  revertConversions (EGenCallExpr gce) table locs =
    EGenCallExpr $ revertConversions gce table locs

instance RevertConversions ExprAtomTail where
  revertConversions (ExprAtomTail aat eat) table locs =
    ExprAtomTail (revertConversions aat table locs) (revertConversions eat table locs)
  revertConversions EATNothing _ _ = EATNothing

instance RevertConversions NumExpr where
  revertConversions (NumExpr e) table locs = NumExpr $ revertConversions e table locs

instance RevertConversions NumExpr4 where
  revertConversions (NPlus e1 e2) table locs =
    NPlus (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NMinus e1 e2) table locs =
    NMinus (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NNumExpr3 e) table locs = NNumExpr3 $ revertConversions e table locs

instance RevertConversions NumExpr3 where
  revertConversions (NStar e1 e2) table locs =
    NStar (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NDiv e1 e2) table locs =
    NDiv (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NMod e1 e2) table locs =
    NMod (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NSlash e1 e2) table locs =
    NSlash (revertConversions e1 table locs) (revertConversions e2 table locs)
  revertConversions (NNumExpr1 e) table locs = NNumExpr1 $ revertConversions e table locs

instance RevertConversions NumExpr1 where
  revertConversions (NIdent i e1 ea) table locs =
    NIdent
    (revertConversions i table locs)
    (revertConversions e1 table locs)
    (revertConversions ea table locs)
  revertConversions (NNumExprAtom ea) table locs =
    NNumExprAtom $ revertConversions ea table locs

instance RevertConversions NumExprAtom where
  revertConversions (NumExprAtom eah eat as) table locs =
    NumExprAtom
    (revertConversions eah table locs)
    (revertConversions eat table locs)
    (revertConversions as table locs)

instance RevertConversions NumExprAtomHead where
  revertConversions (NBuiltinNumUnOp buo ea) table locs =
    NBuiltinNumUnOp buo $ revertConversions ea table locs
  revertConversions (NNumExpr e) table locs =
    NNumExpr $ revertConversions e table locs
  revertConversions (NIdentOrQuotedOp ioqo) table locs =
    NIdentOrQuotedOp $ revertConversions ioqo table locs
  revertConversions x@(NIntLiteral _) _ _ = x
  revertConversions x@(NFloatLiteral _) _ _ = x
  revertConversions (NIfThenElseExpr itee) table locs =
    NIfThenElseExpr $ revertConversions itee table locs
  revertConversions (NLetExpr le) table locs =
    NLetExpr $ revertConversions le table locs
  revertConversions (NCallExpr ce) table locs =
    NCallExpr $ revertConversions ce table locs
  revertConversions (NGenCallExpr gce) table locs =
    NGenCallExpr $ revertConversions gce table locs

instance RevertConversions SetLiteral where
  revertConversions (SetLiteral es) table locs =
    SetLiteral $ map (\x -> revertConversions x table locs) es

instance RevertConversions SetComp where
  revertConversions (SetComp e ct) table locs =
    let locs' = locs ++ locals ct
    in SetComp (revertConversions e table locs') (revertConversions ct table locs)

instance RevertConversions CompTail where
  revertConversions (CompTail gs Nothing) table locs =
    CompTail (map (\x -> revertConversions x table locs) gs) Nothing
  revertConversions (CompTail gs (Just e)) table locs =
    CompTail
    (map (\x -> revertConversions x table locs) gs)
    (Just (revertConversions e table locs))

instance RevertConversions Generator where
  revertConversions (Generator is e) table locs =
    Generator is (revertConversions e table locs)

instance RevertConversions ArrayLiteral where
  revertConversions (ArrayLiteral es) table locs =
    ArrayLiteral $ map (\x -> revertConversions x table locs) es

instance RevertConversions ArrayComp where
  revertConversions ac@(ArrayComp e ct) table locs =
    let locs' = locs ++ locals ct
    in ArrayComp (revertConversions e table locs')
                 (revertConversions ct table locs)

instance RevertConversions ArrayAccessTail where
  revertConversions (ArrayAccessTail es) table locs =
    ArrayAccessTail $ map (\x -> revertConversions x table locs) es

instance RevertConversions IfThenElseExpr where
  revertConversions (IfThenElseExpr c e ces ee) table locs =
    IfThenElseExpr
    (revertConversions c table locs)
    (revertConversions e table locs)
    cesRevertConversionss
    (revertConversions ee table locs)
    where cesRevertConversionss =
            map
            (\(c,e) -> (revertConversions c table locs, revertConversions e table locs))
            ces

instance RevertConversions CallExpr where
  revertConversions ce@(CallExpr ioqo es) table locs =
    CallExpr
    (revertConversions ioqo table locs)
    (map (\x -> revertConversions x table locs) es)

instance RevertConversions LetExpr where
  revertConversions (LetExpr lis e) table locs =
    let locs' = locs ++ concatMap locals lis
    in LetExpr
       (map (\x -> revertConversions x table locs) lis)
       (revertConversions e table locs')

instance RevertConversions LetItem where
  revertConversions (LVarDeclItem vdi) table locs =
    LVarDeclItem $ revertConversions vdi table locs
  revertConversions (LConstraintItem ci) table locs =
    LConstraintItem $ revertConversions ci table locs

instance RevertConversions GenCallExpr where
  revertConversions gce@(GenCallExpr ioqo ct e) table locs =
    let locs' = locs ++ locals ct
    in GenCallExpr
       (revertConversions ioqo table locs)
       (revertConversions ct table locs)
       (revertConversions e table locs')

instance RevertConversions Ident where
  revertConversions i table locs = f table
    where f [] = i
          f ((old, new):rest) = if i == old
                                 && i `notElem` locs
                                 && new `elem` locs
                                   then new
                                   else f rest

instance RevertConversions IdentOrQuotedOp where
  revertConversions (IIdent i) table locs = IIdent $ revertConversions i table locs

instance RevertConversions Annotations where
  revertConversions (Annotations as) table locs =
    Annotations $ map (\x -> revertConversions x table locs) as

instance RevertConversions Annotation where
  revertConversions (Annotation eah eat) table locs =
    Annotation (revertConversions eah table locs) (revertConversions eat table locs)
