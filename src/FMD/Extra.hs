module FMD.Extra where

import FMD
import CST
import CST.Utils

import Data.List (nub)

import Debug.Trace (trace)

lisToLocalDecls :: [LetItem] -> [Declaration]
lisToLocalDecls [] = []
lisToLocalDecls (LConstraintItem _:lis) = lisToLocalDecls lis
lisToLocalDecls (LVarDeclItem (VarDeclItem teai _ _):lis) =
  mkDecl teai : lisToLocalDecls lis

ctToLocalDecls :: CompTail -> Environment -> [Declaration] -> [Declaration]
ctToLocalDecls (CompTail gs _) = gsToLocalDecls gs

gsToLocalDecls :: [Generator] -> Environment -> [Declaration] -> [Declaration]
gsToLocalDecls [] _ _ = []
gsToLocalDecls (Generator [] _:gs) env locs = gsToLocalDecls gs env locs
gsToLocalDecls (Generator (i:is) e:gs) env locs =
  let decl = Declaration (toType e env locs) i
      locs' = decl : locs
  in decl : gsToLocalDecls (Generator is e:gs) env locs'

hasLocal :: Identifiers a => a -> Environment -> [Declaration] -> Bool
hasLocal x env locs = any f ids
  where ids = identifiers x
        f i = case findDecl env1 i of
                Just decl -> decl `elem` locs
                _ -> False
        env1 = foldl (\env decl -> insertDeclaration decl env) env locs

class Types a where
  isBool :: a -> Environment -> Bool
  isVar :: a -> Environment -> [Declaration] -> Bool
  toVarPar :: a -> Environment -> [Declaration] -> VarPar
  toType :: a -> Environment -> [Declaration] -> BaseTiExpr

  toVarPar x env locs = if isVar x env locs
                          then Var
                          else Par

identToUnion :: Ident -> Ident -> Expr6
identToUnion i1 i2 = let f :: Ident -> Expr5
                         f i = EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
                               EExprAtom (ExprAtom
                                           (EIdentOrQuotedOp (IIdent i))
                                           EATNothing
                                           (Annotations []))
                in EUnion (EExpr5 $ f i1) (f i2)

exprToUnion :: Expr -> Expr -> Expr6
exprToUnion e1 e2 = let f :: Expr -> Expr5
                        f e = EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
                              EExprAtom (ExprAtom
                                          (EExpr e)
                                          EATNothing
                                          (Annotations []))
                in EUnion (EExpr5 $ f e1) (f e2)

esToSet :: [Expr] -> Expr
esToSet es = Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
             EExpr7 $ EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $
             EExpr2 $ EExpr1 $ EExprAtom
             (ExprAtom
               (ESetLiteral (SetLiteral es))
               EATNothing
               (Annotations []))

toExprRange :: ToExpr a => a -> a -> Expr
toExprRange x y = let f :: Expr -> Expr4
                      f e = EExpr3 $ EExpr2 $ EExpr1 $
                            EExprAtom (ExprAtom
                                        (EExpr e)
                                        EATNothing
                                        (Annotations []))
                  in Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $
                     EExpr7 $ EExpr6 $ EExpr5 $
                     EEllipsis (f $ toExpr x) (f $ toExpr y)

combineStet :: SetTiExprTail -> SetTiExprTail -> SetTiExprTail
combineStet SInt SInt = SInt
combineStet SInt _ = SInt
combineStet _ SInt = SInt
combineStet (SSet es1) (SSet es2) =
  if es1 == es2
    then SSet es1
    else SSet (nub $ es1 ++ es2)
combineStet stet1@(SRange ne11 ne12) stet2@(SRange ne21 ne22) =
  if stet1 == stet2
    then SRange ne11 ne12
    else SExpr6 $
           exprToUnion
           (toExprRange ne11 ne12)
           (toExprRange ne21 ne22)
combineStet (SExpr6 e1) (SExpr6 e2) =
  if e1 == e2
    then SExpr6 e1
    else SExpr6 $
           exprToUnion
           (toExpr e1)
           (toExpr e2)
combineStet (SSet es) (SRange ne1 ne2) =
  SExpr6 $ exprToUnion (esToSet es) (toExprRange ne1 ne2)
combineStet (SRange ne1 ne2) (SSet es) =
  SExpr6 $ exprToUnion (toExprRange ne1 ne2) (esToSet es)
combineStet (SSet es) (SExpr6 e) =
  SExpr6 $ exprToUnion (esToSet es) (toExpr e)
combineStet (SExpr6 e) (SSet es) =
  SExpr6 $ exprToUnion (toExpr e) (esToSet es)
combineStet (SRange ne1 ne2) (SExpr6 e) =
  SExpr6 $ exprToUnion (toExprRange ne1 ne2) (toExpr e)
combineStet (SExpr6 e)(SRange ne1 ne2)  =
  SExpr6 $ exprToUnion (toExpr e) (toExprRange ne1 ne2)

combineTypes :: BaseTiExpr -> BaseTiExpr -> BaseTiExpr
combineTypes (BaseTiExpr Var btet1) (BaseTiExpr Par btet2) =
  combineTypes (BaseTiExpr Var btet1) (BaseTiExpr Var btet2)
combineTypes (BaseTiExpr Par btet1) (BaseTiExpr Var btet2) =
  combineTypes (BaseTiExpr Var btet1) (BaseTiExpr Var btet2)
combineTypes (BaseTiExpr vp (BIdent i1)) (BaseTiExpr _ (BIdent i2)) =
  if i1 == i2
    then BaseTiExpr vp (BIdent i1)
    else BaseTiExpr vp (BExpr6 $ identToUnion i1 i2)
combineTypes (BaseTiExpr vp BBool) (BaseTiExpr _ BBool) =
  BaseTiExpr vp BBool
combineTypes (BaseTiExpr vp BInt) (BaseTiExpr _ BInt) =
  BaseTiExpr vp BInt
combineTypes (BaseTiExpr vp BFloat) (BaseTiExpr _ BFloat) =
  BaseTiExpr vp BFloat
combineTypes (BaseTiExpr vp (BSetTiExprTail stet1))
             (BaseTiExpr _ (BSetTiExprTail stet2)) =
  BaseTiExpr vp $ BSetTiExprTail $ combineStet stet1 stet2
combineTypes (BaseTiExpr vp (BArrayTiExprTail atet1))
             (BaseTiExpr _ (BSetTiExprTail atet2)) =
  BaseTiExpr vp (BArrayTiExprTail atet1) -- TODO!!!
combineTypes (BaseTiExpr vp (BSet es1)) (BaseTiExpr _ (BSet es2)) =
  if es1 == es2
    then BaseTiExpr vp (BSet es1)
    else BaseTiExpr vp (BExpr6 $ exprToUnion (esToSet es1) (esToSet es2))
combineTypes (BaseTiExpr vp (BIdent i1)) (BaseTiExpr _ (BSet es2)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (toExpr i1) (esToSet es2))
combineTypes (BaseTiExpr vp (BSet es1)) (BaseTiExpr _ (BIdent i2)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (esToSet es1) (toExpr i2))
combineTypes (BaseTiExpr vp btet1@(BRange ne11 ne12))
             (BaseTiExpr _ btet2@(BRange ne21 ne22)) =
  if btet1 == btet2
    then BaseTiExpr vp (BRange ne11 ne12)
    else BaseTiExpr vp (BExpr6 $
                         exprToUnion
                         (toExprRange ne11 ne12)
                         (toExprRange ne21 ne22))
combineTypes (BaseTiExpr vp (BIdent i)) (BaseTiExpr _ (BRange ne1 ne2)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (toExpr i)
                  (toExprRange ne1 ne2))
combineTypes (BaseTiExpr vp (BRange ne1 ne2)) (BaseTiExpr _ (BIdent i)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (toExprRange ne1 ne2)
                  (toExpr i))
combineTypes (BaseTiExpr vp (BSet es)) (BaseTiExpr _ (BRange ne1 ne2)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (esToSet es)
                  (toExprRange ne1 ne2))
combineTypes (BaseTiExpr vp (BRange ne1 ne2)) (BaseTiExpr _ (BSet es)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (toExprRange ne1 ne2)
                  (esToSet es))
combineTypes (BaseTiExpr vp btet1@(BExpr6 e1))
             (BaseTiExpr _ btet2@(BExpr6 e2)) =
  if btet1 == btet2
    then BaseTiExpr vp (BExpr6 e1)
    else BaseTiExpr vp (BExpr6 $ exprToUnion (toExpr e1) (toExpr e2))
combineTypes (BaseTiExpr vp (BExpr6 e)) (BaseTiExpr _ (BIdent i)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (toExpr e) (toExpr i))
combineTypes (BaseTiExpr vp (BIdent i)) (BaseTiExpr _ (BExpr6 e)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (toExpr i) (toExpr e))
combineTypes (BaseTiExpr vp (BExpr6 e)) (BaseTiExpr _ (BSet es)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (toExpr e) (esToSet es))
combineTypes (BaseTiExpr vp (BSet es)) (BaseTiExpr _ (BExpr6 e)) =
  BaseTiExpr vp (BExpr6 $ exprToUnion (esToSet es) (toExpr e))
combineTypes (BaseTiExpr vp (BExpr6 e)) (BaseTiExpr _ (BRange ne1 ne2)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (toExpr e)
                  (toExprRange ne1 ne2))
combineTypes (BaseTiExpr vp (BRange ne1 ne2)) (BaseTiExpr _ (BExpr6 e)) =
  BaseTiExpr vp (BExpr6 $
                  exprToUnion
                  (toExprRange ne1 ne2)
                  (toExpr e))
combineTypes a b = error $ "Types cannot be combined: `" ++ show a ++ "' and `" ++ show b ++ "'."

toSetType :: BaseTiExpr -> BaseTiExpr
toSetType (BaseTiExpr vp BInt) = BaseTiExpr vp $ BSetTiExprTail SInt
toSetType (BaseTiExpr vp (BSet es)) = BaseTiExpr vp $ BSetTiExprTail (SSet es)
toSetType (BaseTiExpr vp (BRange ne1 ne2)) =
  BaseTiExpr vp $ BSetTiExprTail (SRange ne1 ne2)

stripArrayType :: BaseTiExpr -> ExprAtomTail -> Environment -> [Declaration]
               -> BaseTiExpr
stripArrayType bte EATNothing env locs = bte
stripArrayType bte1 (ExprAtomTail (ArrayAccessTail es) eat) env locs =
  stripArrayType bte2 eat env locs
  where bte2 = stripArrayType' bte1 (length es)

stripArrayType' :: BaseTiExpr -> Int -> BaseTiExpr
stripArrayType' (BaseTiExpr vp (BArrayTiExprTail (ArrayTiExprTail tes te))) d =
  if length tes == d
    then bte
    else BaseTiExpr vp (BArrayTiExprTail (ArrayTiExprTail
                                           (take
                                             (length tes - d)
                                             tes)
                                           te))
  where TiExpr bte = te

instance Types TiExprAndId where
  isBool _ _ = False

instance Types VarDeclItem where
  isBool _ _ = False

instance Types ConstraintItem where
  isBool _ _ = True
  isVar (ConstraintItem e) = isVar e
  toType (ConstraintItem e) env locs = BaseTiExpr (toVarPar e env locs) BBool

instance Types BaseTiExpr where
 isVar (BaseTiExpr Var _) _ _= True
 isVar (BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail _ (TiExpr (BaseTiExpr Var _))))) _ _ = True
 isVar _ _ _= False

instance Types BaseTiExprTail where
  isBool _ _ = False

instance Types Expr where
  isBool (Expr e) = isBool e
  isVar (Expr e) = isVar e
  toType (Expr e) = toType e

instance Types Expr12 where
  isBool (EExpr11 e) env = isBool e env
  isBool _ _ = True
  isVar (EEquivalence e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr11 e) env locs = isVar e env locs
  toType ee@(EEquivalence _ _) env locs =
    BaseTiExpr (toVarPar ee env locs) BBool
  toType (EExpr11 e) env locs = toType e env locs

instance Types Expr11 where
  isBool (EExpr10 e) env = isBool e env
  isBool _ _ = True
  isVar (ERImplies e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ELImplies e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr10 e) env locs = isVar e env locs
  toType (EExpr10 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BBool

instance Types Expr10 where
  isBool (EExpr9 e) env = isBool e env
  isBool _ _ = True
  isVar (EOr e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EXor e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr9 e) env locs = isVar e env locs
  toType (EExpr9 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BBool

instance Types Expr9 where
  isBool (EExpr8 e) env = isBool e env
  isBool _ _ = True
  isVar (EAnd e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr8 e) env locs = isVar e env locs
  toType (EExpr8 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BBool

instance Types Expr8 where
  isBool (EExpr7 e) env = isBool e env
  isBool _ _ = True
  isVar (ELt e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EGt e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ELeq e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EGeq e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EEqEq e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EEq e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ENeq e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr7 e) env locs = isVar e env locs
  toType (EExpr7 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BBool

instance Types Expr7 where
  isBool (EExpr6 e) env = isBool e env
  isBool _ _ = True
  isVar (EIn e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ESubset e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ESuperset e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr6 e) env locs = isVar e env locs
  toType (EExpr6 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BBool

instance Types Expr6 where
  isBool (EExpr5 e) env = isBool e env
  isBool _ _ = False
  isVar (EUnion e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EDiff e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ESymDiff e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr5 e) env locs = isVar e env locs
  toType (EUnion e1 e2) env locs = combineTypes
                                     (toType e1 env locs)
                                     (toType e2 env locs)
  toType (EDiff e1 e2) env locs = combineTypes
                                    (toType e1 env locs)
                                    (toType e2 env locs)
  toType (ESymDiff e1 e2) env locs = combineTypes
                                       (toType e1 env locs)
                                       (toType e2 env locs)
  toType (EExpr5 e) env locs = toType e env locs

instance Types Expr5 where
  isBool (EExpr4 e) env = isBool e env
  isBool _ _ = False
  isVar (EEllipsis e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr4 e) env locs = isVar e env locs
  toType (EExpr4 e) env locs = toType e env locs
  toType ee@(EEllipsis e1 e2) env locs =
    BaseTiExpr
    (toVarPar ee env locs)
    (BSetTiExprTail $ SRange (toNumExpr $ toExpr e1) (toNumExpr $ toExpr e2))

instance Types Expr4 where
  isBool (EExpr3 e) env = isBool e env
  isBool _ _ = False
  isVar (EPlus e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EMinus e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr3 e) env locs = isVar e env locs
  toType (EExpr3 e) env locs = toType e env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BInt -- TODO: smarter domain?

instance Types Expr3 where
  isBool (EExpr2 e) env = isBool e env
  isBool _ _ = False
  isVar (EStar e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EDiv e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EMod e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (ESlash e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EIntersect e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr2 e) env locs = isVar e env locs
  toType (EExpr2 e) env locs = toType e env locs
  toType ee@(EIntersect _ _) env locs = toSetType $ toType ee env locs
  toType ee env locs = BaseTiExpr (toVarPar ee env locs) BInt -- TODO: smarter domain?

instance Types Expr2 where
  isBool (EExpr1 e) env = isBool e env
  isBool _ _ = False
  isVar (EPlusPlus e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExpr1 e) env locs = isVar e env locs
  toType (EExpr1 e) env locs = toType e env locs
--  toType ee env locs = undefined -- TODO: array type?

instance Types Expr1 where
  isBool (EExprAtom ea) env = isBool ea env
  isBool (EIdent i _ _) env = isBool i env
  isVar (EIdent _ e1 e2) env locs = isVar e1 env locs || isVar e2 env locs
  isVar (EExprAtom ea) env locs = isVar ea env locs
  toType (EExprAtom ea) env locs = toType ea env locs
  toType (EIdent i _ _) env locs = case findDef env i of
    Just (Definition bte _ _ _) -> bte

instance Types ExprAtom where
  isBool (ExprAtom eah EATNothing _) env = isBool eah env
  isBool (ExprAtom _eah _eat _) _ = False -- TODO: how to handle bool array
                                            --       with array access?
  isVar (ExprAtom eah EATNothing _) env locs = isVar eah env locs
  isVar (ExprAtom eah eat _) env locs = isVar eah env locs || isVar eat env locs
  toType (ExprAtom eah EATNothing _) env locs = toType eah env locs
  toType (ExprAtom eah eat _) env locs =
    stripArrayType (toType eah env locs) eat env locs

instance Types ExprAtomHead where
  isBool (EBuiltinUnOp BNot _) _ = True
  isBool (EBuiltinUnOp _ _ea) _ = False
  isBool (EExpr e) env = isBool e env
  isBool (EIdentOrQuotedOp _) _ = False
  isBool (EBoolLiteral _) _ = True
  isBool (EIntLiteral _) _ = False
  isBool (EFloatLiteral _) _ = False
  isBool (ESetLiteral _) _ = False
  isBool (ESetComp _) _ = False
  isBool (EArrayLiteral _) _ = False
  isBool (EArrayComp _) _ = False
  isBool (EIfThenElseExpr itee) env = isBool itee env
  isBool (ELetExpr le) env = isBool le env
  isBool (ECallExpr ce) env = isBool ce env
  isBool (EGenCallExpr gce) env = isBool gce env
  isVar (EBuiltinUnOp _ ea) env locs = isVar ea env locs
  isVar (EExpr e) env locs = isVar e env locs
  isVar (EIdentOrQuotedOp ioqo) env locs = isVar ioqo env locs
  isVar (EBoolLiteral _) _ _ = False
  isVar (EIntLiteral _) _ _ = False
  isVar (EFloatLiteral _) _ _ = False
  isVar (ESetLiteral sl) env locs = isVar sl env locs
  isVar (ESetComp sc) env locs = isVar sc env locs
  isVar (EArrayLiteral al) env locs = isVar al env locs
  isVar (EArrayComp ac) env locs = isVar ac env locs
  isVar (EIfThenElseExpr itee) env locs = isVar itee env locs
  isVar (ELetExpr le) env locs = isVar le env locs
  isVar (ECallExpr ce) env locs = isVar ce env locs
  isVar (EGenCallExpr gce) env locs = isVar gce env locs
  toType (EBuiltinUnOp BNot ea) env locs =
    BaseTiExpr (toVarPar ea env locs) BBool
  toType (EBuiltinUnOp _ ea) env locs =
    BaseTiExpr (toVarPar ea env locs) BInt
  toType (EExpr e) env locs = toType e env locs
  toType (EIdentOrQuotedOp ioqo) env locs = toType ioqo env locs
  toType (EBoolLiteral _) _ _ =
    BaseTiExpr Par BBool
  toType (EIntLiteral _) _ _ =
    BaseTiExpr Par BInt
  toType (EFloatLiteral _) _ _ =
    BaseTiExpr Par BFloat
  toType (ESetLiteral sl) env locs = toType sl env locs
  toType (ESetComp sc) env locs = toType sc env locs
  toType (EArrayLiteral al) env locs = toType al env locs
  toType (EArrayComp ac) env locs = toType ac env locs
  toType (EIfThenElseExpr itee) env locs = toType itee env locs
  toType (ELetExpr le) env locs = toType le env locs
  toType (ECallExpr ce) env locs = toType ce env locs
  toType (EGenCallExpr gce) env locs = toType gce env locs

instance Types ExprAtomTail where
  isBool _ _ = False
  isVar (ExprAtomTail aat eat) env locs = isVar aat env locs || isVar eat env locs
  isVar EATNothing _ _ = False
--  toType _ _ = undefined -- TODO: array something

instance Types NumExpr where
  isBool (NumExpr ne) = isBool ne

instance Types NumExpr4 where
  isBool (NNumExpr3 ne) env = isBool ne env
  isBool _ _ = False

instance Types NumExpr3 where
  isBool (NNumExpr1 ne) env = isBool ne env
  isBool _ _ = False

instance Types NumExpr1 where
  isBool (NNumExprAtom nea) env = isBool nea env
  isBool _ _ = False

instance Types NumExprAtom where
  isBool (NumExprAtom neah _ _) = isBool neah

instance Types NumExprAtomHead where
  isBool (NBuiltinNumUnOp _ _) _ = False
  isBool (NNumExpr ne) env = isBool ne env
  isBool (NIdentOrQuotedOp _) _ = False
  isBool (NIntLiteral _) _ = False
  isBool (NFloatLiteral _) _ = False
  isBool (NIfThenElseExpr itee) env = isBool itee env
  isBool (NLetExpr le) env = isBool le env
  isBool (NCallExpr ce) env = isBool ce env
  isBool (NGenCallExpr gce) env = isBool gce env

instance Types SetLiteral where
  isBool _ _ = False
 --  isVar (SetLiteral es) env locs = undefined
  toType (SetLiteral es) _ _ = BaseTiExpr Var (BSetTiExprTail $ SSet es)

instance Types SetComp where
  isBool _ _ = False
  isVar (SetComp e ct) env locs =
    isVar e env locs1 || isVar ct env locs1
    where locs1 = ctToLocalDecls ct env locs ++ locs
  toType sc env locs =
    BaseTiExpr (toVarPar sc env locs) $ BSetTiExprTail SInt -- TODO: smarter?

instance Types CompTail where
  isBool _ _ = False
  isVar (CompTail gs Nothing) env locs =
    any (\x -> isVar x env locs) gs
  isVar (CompTail gs (Just e)) env locs =
    any (\x -> isVar x env locs) gs || isVar e env locs
  toType (CompTail [g] _) env locs = toType g env locs
  toType _ _ _ = BaseTiExpr Par BInt

instance Types Generator where
  isBool _ _ = False
  isVar (Generator _ e) = isVar e
  toType (Generator _ e) _ _ = toBte e

instance Types ArrayLiteral where
  isBool _ _ = False
  isVar (ArrayLiteral es) env locs = any (\x -> isVar x env locs) es
  toType (ArrayLiteral []) _ _ =
    BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail [dim] dom))
    where dim = TiExpr $ BaseTiExpr Par (BSet [])
          dom = TiExpr $ BaseTiExpr Par (BSet [])
  toType (ArrayLiteral (e:es)) env locs =
    BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail [dim] dom))
    where dim = TiExpr $ BaseTiExpr Par
                (BRange (toNumExpr $ toExpr (1::Int))
                        (toNumExpr $ toExpr (length es + 1::Int)))
          dom = TiExpr $ foldl
                  combineTypes
                  (toType e env locs)
                  (map (\x -> toType x env locs) es)

instance Types ArrayComp where
  isBool _ _ = False
  isVar (ArrayComp e ct) env locs =
    isVar e env locs1 || isVar ct env locs1
    where locs1 = ctToLocalDecls ct env locs ++ locs
  toType (ArrayComp e ct) env locs =
    BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail [dim] dom))
    where dim = TiExpr $ toType ct env locs1
          dom = TiExpr $ toType e env locs1
          locs1 = ctToLocalDecls ct env locs ++ locs

instance Types ArrayAccessTail where
  isBool _ _ = False
  isVar (ArrayAccessTail es) env locs = any (\x -> isVar x env locs) es
--  toType _ _ = undefined

instance Types IfThenElseExpr where
  isBool (IfThenElseExpr _ e _ _) = isBool e
  isVar (IfThenElseExpr c e ces ee) env locs =
    isVar c env locs ||
    isVar e env locs ||
    any (\(x,y) -> isVar x env locs ||
                   isVar y env locs) ces ||
    isVar ee env locs
  toType (IfThenElseExpr _ e _ _) = toType e

instance Types CallExpr where
  isBool (CallExpr i _) = isBool i
  isVar (CallExpr (IIdent i) es) env locs =
    case findDef env i of
      Just (Definition (BaseTiExpr Var _) _ _ _) -> True
      _ -> any (\x -> isVar x env locs) es
  toType (CallExpr (IIdent i) _) env locs =
    case findDef env i of
      Just (Definition bte _ _ _) -> bte
      _ -> error $ "Error, function/predicate symbol `" ++ show i ++ "' not found!"

instance Types LetExpr where
  isBool (LetExpr lis e) env = isBool e env
  isVar (LetExpr lis e) env locs =
    any (\x -> isVar x env locs1) lis || isVar e env locs1
    where locs1 = lisToLocalDecls lis ++ locs
  toType (LetExpr lis e) env locs =
    toType e env locs1
    where locs1 = lisToLocalDecls lis ++ locs

instance Types LetItem where
  isBool _ _ = False
  isVar (LConstraintItem ci) env locs = isVar ci env locs
  isVar _ _ _ = False
  toType (LConstraintItem ci) env locs = toType ci env locs
  toType (LVarDeclItem vdi) env locs = toType vdi env locs

instance Types GenCallExpr where
  isBool (GenCallExpr i _ _) = isBool i
  isVar (GenCallExpr _ ct e) env locs =
    isVar ct env locs1 || isVar e env locs1
    where locs1 = ctToLocalDecls ct env locs ++ locs
  toType (GenCallExpr _ ct e) env locs =
    toType e env locs1
    where locs1 = ctToLocalDecls ct env locs ++ locs

instance Types Ident where
  isBool i env = case findDecl env i of
                     Just decl -> isBoolDecl decl
                     Nothing -> case findDef env i of
                                  Just def -> isBoolDef def
                                  Nothing -> False
  isVar i env locs = case findDecl env1 i of
    Just (Declaration bte _) -> isVar bte env locs
    _ -> error ("Error! Declaration for `" ++ show i ++ "' not found." ++
                "\nWith Env: " ++ show env ++
                "\n  Locals: " ++ show locs)
    where env1 = foldl (\env decl -> insertDeclaration decl env) env locs
  toType i env locs = case findDecl env1 i of
    Just (Declaration bte _) -> bte
    _ -> error
         ("Error! Declaration for `" ++ show i ++ "' not found." ++
          "\nWith Env: " ++ show env ++
          "\n  Locals: " ++ show locs)
    where env1 = foldl (\env decl -> insertDeclaration decl env) env locs

instance Types IdentOrQuotedOp where
  isBool (IIdent i) = isBool i
  isVar (IIdent i) = isVar i
  toType (IIdent i) = toType i
