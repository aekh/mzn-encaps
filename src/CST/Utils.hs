{-| -}

module CST.Utils where

import CST
import Debug.Trace

constraints :: CST -> [Expr]
constraints (Model []) = []
constraints (Model ((IConstraintItem (ConstraintItem e)):is)) =
  e : constraints (Model is)
constraints (Model (_:is)) = constraints (Model is)

{-
boolIdents :: CST -> [Ident]
boolIdents (Model []) = Ident <$> basePreds
boolIdents (Model ((IPredicateItem
                    (PredicateItem (OperationItemTail i _ _ _))):is)) =
  i : boolIdents (Model is)
boolIdents (Model ((IVarDeclItem
                    (VarDeclItem
                     (TiExprAndId (TiExpr (BaseTiExpr _ BBool)) i) _ _)):is)) =
  i : boolIdents (Model is)
boolIdents (Model (_:is)) = boolIdents (Model is)

basePreds :: [String]
basePreds = ["forall"
            ,"exist"
            ,"alldifferent"
            ,"all_different"]
-}

class Substitute x where
  substitute :: x -> Ident -> Ident -> [Ident] -> x

instance Substitute TiExprAndId where
  substitute (TiExprAndId (TiExpr bte) i) old new locs =
    TiExprAndId (TiExpr $ substitute bte old new locs) i

instance Substitute VarDeclItem where
  substitute (VarDeclItem teai as mE) old new locs =
    VarDeclItem
    (substitute teai old new locs)
    (substitute as old new locs)
    ((\x -> substitute x old new locs) <$> mE )

instance Substitute ConstraintItem where
  substitute (ConstraintItem e) old new locs =
    ConstraintItem $ substitute e old new locs

instance Substitute BaseTiExpr where
  substitute (BaseTiExpr vp btet) old new locs =
    BaseTiExpr vp $ substitute btet old new locs

instance Substitute BaseTiExprTail where
  substitute (BIdent i) old new locs =
    BIdent $ substitute i old new locs
  substitute (BSetTiExprTail stet) old new locs =
    trace "substitute on BSetTiExprTail not implemented!" undefined
    -- BSetTiExprTail$ substitute stet old new locs
  substitute (BArrayTiExprTail atet) old new locs =
    trace "substitute on BArrayTiExprTail not implemented!" undefined
    -- BArrayTiExprTail $ substitute atet old new locs
  substitute (BSet es) old new locs =
    BSet $ map (\x -> substitute x old new locs) es
  substitute (BRange ne1 ne2) old new locs =
    BRange (substitute ne1 old new locs) (substitute ne2 old new locs)
  substitute (BExpr6 e) old new locs =
    BExpr6 $ substitute e old new locs
  substitute btet _ _ _ = btet

instance Substitute Expr where
  substitute (Expr e) old new locs = Expr $ substitute e old new locs

instance Substitute Expr12 where
  substitute (EEquivalence e1 e2) old new locs =
    EEquivalence (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr11 e) old new locs = EExpr11 $ substitute e old new locs

instance Substitute Expr11 where
  substitute (ERImplies e1 e2) old new locs =
    ERImplies (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ELImplies e1 e2) old new locs =
    ELImplies (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr10 e) old new locs = EExpr10 $ substitute e old new locs

instance Substitute Expr10 where
  substitute (EOr e1 e2) old new locs =
    EOr (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EXor e1 e2) old new locs =
    EXor (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr9 e) old new locs = EExpr9 $ substitute e old new locs

instance Substitute Expr9 where
  substitute (EAnd e1 e2) old new locs =
    EAnd (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr8 e) old new locs = EExpr8 $ substitute e old new locs

instance Substitute Expr8 where
  substitute (ELt e1 e2) old new locs =
    ELt (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EGt e1 e2) old new locs =
    EGt (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ELeq e1 e2) old new locs =
    ELeq (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EGeq e1 e2) old new locs =
    EGeq (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EEqEq e1 e2) old new locs =
    EEqEq (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EEq e1 e2) old new locs =
    EEq (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ENeq e1 e2) old new locs =
    ENeq (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr7 e) old new locs = EExpr7 $ substitute e old new locs

instance Substitute Expr7 where
  substitute (EIn e1 e2) old new locs =
    EIn (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ESubset e1 e2) old new locs =
    ESubset (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ESuperset e1 e2) old new locs =
    ESuperset (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr6 e) old new locs = EExpr6 $ substitute e old new locs

instance Substitute Expr6 where
  substitute (EUnion e1 e2) old new locs =
    EUnion (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EDiff e1 e2) old new locs =
    EDiff (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ESymDiff e1 e2) old new locs =
    ESymDiff (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr5 e) old new locs = EExpr5 $ substitute e old new locs

instance Substitute Expr5 where
  substitute (EEllipsis e1 e2) old new locs =
    EEllipsis (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr4 e) old new locs = EExpr4 $ substitute e old new locs

instance Substitute Expr4 where
  substitute (EPlus e1 e2) old new locs =
    EPlus (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EMinus e1 e2) old new locs =
    EMinus (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr3 e) old new locs = EExpr3 $ substitute e old new locs

instance Substitute Expr3 where
  substitute (EStar e1 e2) old new locs =
    EStar (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EDiv e1 e2) old new locs =
    EDiv (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EMod e1 e2) old new locs =
    EMod (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (ESlash e1 e2) old new locs =
    ESlash (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EIntersect e1 e2) old new locs =
    EIntersect (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr2 e) old new locs = EExpr2 $ substitute e old new locs

instance Substitute Expr2 where
  substitute (EPlusPlus e1 e2) old new locs =
    EPlusPlus (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (EExpr1 e) old new locs = EExpr1 $ substitute e old new locs

instance Substitute Expr1 where
  substitute (EIdent i e1 ea) old new locs =
    EIdent
    (substitute i old new locs)
    (substitute e1 old new locs)
    (substitute ea old new locs)
  substitute (EExprAtom ea) old new locs =
    EExprAtom $ substitute ea old new locs

instance Substitute ExprAtom where
  substitute (ExprAtom eah eat as) old new locs =
    ExprAtom
    (substitute eah old new locs)
    (substitute eat old new locs)
    (substitute as old new locs)

instance Substitute ExprAtomHead where
  substitute (EBuiltinUnOp buo ea) old new locs =
    EBuiltinUnOp buo $ substitute ea old new locs
  substitute (EExpr e) old new locs =
    EExpr $ substitute e old new locs
  substitute (EIdentOrQuotedOp ioqo) old new locs =
    EIdentOrQuotedOp $ substitute ioqo old new locs
  substitute x@(EBoolLiteral _) _ _ _ = x
  substitute x@(EIntLiteral _) _ _ _ = x
  substitute x@(EFloatLiteral _) _ _ _ = x
  substitute (ESetLiteral sl) old new locs =
    ESetLiteral $ substitute sl old new locs
  substitute (ESetComp sc) old new locs =
    ESetComp $ substitute sc old new locs
  substitute (EArrayLiteral al) old new locs =
    EArrayLiteral $ substitute al old new locs
  substitute (EArrayComp ac) old new locs =
    EArrayComp $ substitute ac old new locs
  substitute (EIfThenElseExpr itee) old new locs =
    EIfThenElseExpr $ substitute itee old new locs
  substitute (ELetExpr le) old new locs =
    ELetExpr $ substitute le old new locs
  substitute (ECallExpr ce) old new locs =
    ECallExpr $ substitute ce old new locs
  substitute (EGenCallExpr gce) old new locs =
    EGenCallExpr $ substitute gce old new locs

instance Substitute ExprAtomTail where
  substitute (ExprAtomTail aat eat) old new locs =
    ExprAtomTail (substitute aat old new locs) (substitute eat old new locs)
  substitute EATNothing _ _ _ = EATNothing

instance Substitute NumExpr where
  substitute (NumExpr e) old new locs = NumExpr $ substitute e old new locs

instance Substitute NumExpr4 where
  substitute (NPlus e1 e2) old new locs =
    NPlus (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NMinus e1 e2) old new locs =
    NMinus (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NNumExpr3 e) old new locs = NNumExpr3 $ substitute e old new locs

instance Substitute NumExpr3 where
  substitute (NStar e1 e2) old new locs =
    NStar (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NDiv e1 e2) old new locs =
    NDiv (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NMod e1 e2) old new locs =
    NMod (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NSlash e1 e2) old new locs =
    NSlash (substitute e1 old new locs) (substitute e2 old new locs)
  substitute (NNumExpr1 e) old new locs = NNumExpr1 $ substitute e old new locs

instance Substitute NumExpr1 where
  substitute (NIdent i e1 ea) old new locs =
    NIdent
    (substitute i old new locs)
    (substitute e1 old new locs)
    (substitute ea old new locs)
  substitute (NNumExprAtom ea) old new locs =
    NNumExprAtom $ substitute ea old new locs

instance Substitute NumExprAtom where
  substitute (NumExprAtom eah eat as) old new locs =
    NumExprAtom
    (substitute eah old new locs)
    (substitute eat old new locs)
    (substitute as old new locs)

instance Substitute NumExprAtomHead where
  substitute (NBuiltinNumUnOp buo ea) old new locs =
    NBuiltinNumUnOp buo $ substitute ea old new locs
  substitute (NNumExpr e) old new locs =
    NNumExpr $ substitute e old new locs
  substitute (NIdentOrQuotedOp ioqo) old new locs =
    NIdentOrQuotedOp $ substitute ioqo old new locs
  substitute x@(NIntLiteral _) _ _ _ = x
  substitute x@(NFloatLiteral _) _ _ _ = x
  substitute (NIfThenElseExpr itee) old new locs =
    NIfThenElseExpr $ substitute itee old new locs
  substitute (NLetExpr le) old new locs =
    NLetExpr $ substitute le old new locs
  substitute (NCallExpr ce) old new locs =
    NCallExpr $ substitute ce old new locs
  substitute (NGenCallExpr gce) old new locs =
    NGenCallExpr $ substitute gce old new locs

instance Substitute SetLiteral where
  substitute (SetLiteral es) old new locs =
    SetLiteral $ map (\x -> substitute x old new locs) es

instance Substitute SetComp where
  substitute (SetComp e ct) old new locs =
    let locs' = locs ++ locals ct
    in SetComp (substitute e old new locs') (substitute ct old new locs)

instance Substitute CompTail where
  substitute (CompTail gs Nothing) old new locs =
    CompTail (map (\x -> substitute x old new locs) gs) Nothing
  substitute (CompTail gs (Just e)) old new locs =
    CompTail
    (map (\x -> substitute x old new locs) gs)
    (Just (substitute e old new locs))

instance Substitute Generator where
  substitute (Generator is e) old new locs =
    Generator is (substitute e old new locs)

instance Substitute ArrayLiteral where
  substitute (ArrayLiteral es) old new locs =
    ArrayLiteral $ map (\x -> substitute x old new locs) es

instance Substitute ArrayComp where
  substitute (ArrayComp e ct) old new locs =
    let locs' = locs ++ locals ct
    in ArrayComp (substitute e old new locs') (substitute ct old new locs)

instance Substitute ArrayAccessTail where
  substitute (ArrayAccessTail es) old new locs =
    ArrayAccessTail $ map (\x -> substitute x old new locs) es

instance Substitute IfThenElseExpr where
  substitute (IfThenElseExpr c e ces ee) old new locs =
    IfThenElseExpr
    (substitute c old new locs)
    (substitute e old new locs)
    cesSubstitutes
    (substitute ee old new locs)
    where cesSubstitutes =
            map
            (\(c,e) -> (substitute c old new locs, substitute e old new locs))
            ces

instance Substitute CallExpr where
  substitute (CallExpr ioqo es) old new locs =
    CallExpr
    (substitute ioqo old new locs)
    (map (\x -> substitute x old new locs) es)

instance Substitute LetExpr where
  substitute (LetExpr lis e) old new locs =
    let locs' = locs ++ concatMap locals lis
    in LetExpr
       (map (\x -> substitute x old new locs) lis)
       (substitute e old new locs')

instance Substitute LetItem where
  substitute (LVarDeclItem vdi) old new locs =
    LVarDeclItem $ substitute vdi old new locs
  substitute (LConstraintItem ci) old new locs =
    LConstraintItem $ substitute ci old new locs

instance Substitute GenCallExpr where -- TODO: LOCALS!!
  substitute (GenCallExpr ioqo ct e) old new locs =
    let locs' = locs ++ locals ct
    in GenCallExpr
       (substitute ioqo old new locs)
       (substitute ct old new locs)
       (substitute e old new locs')

instance Substitute Ident where
  substitute i old new locs = if i == old && i `notElem` locs
                           then new
                           else i

instance Substitute IdentOrQuotedOp where
  substitute (IIdent i) old new locs = IIdent $ substitute i old new locs

instance Substitute Annotations where
  substitute (Annotations as) old new locs =
    Annotations $ map (\x -> substitute x old new locs) as

instance Substitute Annotation where
  substitute (Annotation eah eat) old new locs =
    Annotation (substitute eah old new locs) (substitute eat old new locs)

------------------
-- TYPE FINDING --
------------------

class BteFinder a where
  toBte :: a -> BaseTiExpr

toNumExpr :: Expr -> NumExpr
toNumExpr (Expr (EExpr11 (EExpr10 (EExpr9 (EExpr8 (EExpr7 (EExpr6 (EExpr5
                                                                   (EExpr4 e)
                                                                  )))))))) =
  NumExpr $ toNumExpr4 e
toNumExpr _ = undefined

toNumExpr4 :: Expr4 -> NumExpr4
toNumExpr4 (EPlus e1 e2) = NPlus (toNumExpr4 e1) (toNumExpr3 e2)
toNumExpr4 (EMinus e1 e2) = NMinus (toNumExpr4 e1) (toNumExpr3 e2)
toNumExpr4 (EExpr3 e) = NNumExpr3 $ toNumExpr3 e

toNumExpr3 :: Expr3 -> NumExpr3
toNumExpr3 (EStar e1 (EExpr1 e2)) = NStar (toNumExpr3 e1) (toNumExpr1 e2)
toNumExpr3 (EDiv e1 (EExpr1 e2)) = NDiv (toNumExpr3 e1) (toNumExpr1 e2)
toNumExpr3 (EMod e1 (EExpr1 e2)) = NMod (toNumExpr3 e1) (toNumExpr1 e2)
toNumExpr3 (ESlash e1 (EExpr1 e2)) = NSlash (toNumExpr3 e1) (toNumExpr1 e2)
toNumExpr3 (EExpr2 (EExpr1 e)) = NNumExpr1 $ toNumExpr1 e
toNumExpr3 _ = undefined

toNumExpr1 :: Expr1 -> NumExpr1
toNumExpr1 (EIdent i e ea) = NIdent i (toNumExpr1 e) (toNumExprAtom ea)
toNumExpr1 (EExprAtom ea) = NNumExprAtom $ toNumExprAtom ea

toNumExprAtom :: ExprAtom -> NumExprAtom
toNumExprAtom (ExprAtom eah eat as) = NumExprAtom (toNumExprAtomHead eah) eat as

toNumExprAtomHead :: ExprAtomHead -> NumExprAtomHead
toNumExprAtomHead (EBuiltinUnOp (BBuiltinNumUnOp bnuo) ea) =
  NBuiltinNumUnOp bnuo $ toNumExprAtom ea
toNumExprAtomHead (EExpr e) = NNumExpr $ toNumExpr e
toNumExprAtomHead (EIdentOrQuotedOp ioqo) = NIdentOrQuotedOp ioqo
toNumExprAtomHead (EIntLiteral il) = NIntLiteral il
toNumExprAtomHead (EFloatLiteral fl) = NFloatLiteral fl
toNumExprAtomHead (EIfThenElseExpr itee) = NIfThenElseExpr itee
toNumExprAtomHead (ELetExpr le) = NLetExpr le
toNumExprAtomHead (ECallExpr ce) = NCallExpr ce
toNumExprAtomHead (EGenCallExpr gce) = NGenCallExpr gce
toNumExprAtomHead _ = undefined


instance BteFinder Expr where
  toBte (Expr e) = toBte e

instance BteFinder Expr12 where
  toBte (EExpr11 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr11 where
  toBte (EExpr10 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr10 where
  toBte (EExpr9 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr9 where
  toBte (EExpr8 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr8 where
  toBte (EExpr7 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr7 where
  toBte (EExpr6 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr6 where
  toBte (EUnion e1 e2) =
    BaseTiExpr Par $ BExpr6 (EUnion e1 e2)
  --TODO: Diff and SymDiff
  toBte (EExpr5 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr5 where
  toBte (EEllipsis e1 e2) =
    BaseTiExpr Par $ BRange (NumExpr $ toNumExpr4 e1) (NumExpr $ toNumExpr4 e2)
  toBte (EExpr4 e) = toBte e

instance BteFinder Expr4 where
  toBte (EExpr3 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr3 where
  toBte (EExpr2 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr2 where
  toBte (EExpr1 e) = toBte e
  toBte _ = undefined

instance BteFinder Expr1 where
  toBte (EExprAtom ea) = toBte ea
  toBte _ = undefined

instance BteFinder ExprAtom where
  toBte (ExprAtom eah EATNothing _) = toBte eah
  toBte _ = undefined

instance BteFinder ExprAtomHead where
  toBte (EExpr e) = toBte e
  toBte (EIdentOrQuotedOp ioqo) = toBte ioqo
  toBte (ESetLiteral (SetLiteral es)) =
    BaseTiExpr Par $ BSet es
  toBte _ = undefined

instance BteFinder Ident where
  toBte i = BaseTiExpr Par $ BIdent i

instance BteFinder IdentOrQuotedOp where
  toBte (IIdent i) = toBte i

------------------------
-- TO EXPR CONVERSION --
------------------------

class ToExpr a where
  toExpr :: a -> Expr

instance ToExpr Int where
  toExpr i = toExpr $ IntLiteral i

instance ToExpr Bool where
  toExpr b = toExpr $ BoolLiteral b

instance ToExpr ConstraintItem where
  toExpr (ConstraintItem e) = e

instance ToExpr Expr where
  toExpr e = e

instance ToExpr Expr12 where
  toExpr = Expr

instance ToExpr Expr11 where
  toExpr e =
    Expr $ EExpr11 e

instance ToExpr Expr10 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 e

instance ToExpr Expr9 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 e

instance ToExpr Expr8 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 e

instance ToExpr Expr7 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 e

instance ToExpr Expr6 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 e

instance ToExpr Expr5 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 e

instance ToExpr Expr4 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 e

instance ToExpr Expr3 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 e

instance ToExpr Expr2 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 e

instance ToExpr Expr1 where
  toExpr e =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 e

instance ToExpr ExprAtom where
  toExpr ea =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom ea

instance ToExpr ExprAtomHead where
  toExpr eah =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                eah
                EATNothing
                (Annotations []))

instance ToExpr NumExpr where
  toExpr (NumExpr e) = toExpr e

toExpr4 :: NumExpr4 -> Expr4
toExpr4 (NPlus ne1 ne2) =
  EPlus (toExpr4 ne1) (toExpr3 ne2)
toExpr4 (NMinus ne1 ne2) =
  EMinus (toExpr4 ne1) (toExpr3 ne2)
toExpr4 (NNumExpr3 ne) = EExpr3 $ toExpr3 ne

instance ToExpr NumExpr4 where
  toExpr ne =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ toExpr4 ne

toExpr3 :: NumExpr3 -> Expr3
toExpr3 (NStar ne1 ne2) =
  EStar (toExpr3 ne1) (EExpr1 $ toExpr1 ne2)
toExpr3 (NDiv ne1 ne2) =
  EDiv  (toExpr3 ne1) (EExpr1 $ toExpr1 ne2)
toExpr3 (NMod ne1 ne2) =
  EMod  (toExpr3 ne1) (EExpr1 $ toExpr1 ne2)
toExpr3 (NSlash ne1 ne2) =
  ESlash (toExpr3 ne1) (EExpr1 $ toExpr1 ne2)
toExpr3 (NNumExpr1 ne) = EExpr2 $ EExpr1 $ toExpr1 ne

instance ToExpr NumExpr3 where
  toExpr ne =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ toExpr3 ne

toExpr1 :: NumExpr1 -> Expr1
toExpr1 (NIdent i ne1 ne2) =
  EIdent i (toExpr1 ne1) (toExprAtom ne2)
toExpr1 (NNumExprAtom nea) = EExprAtom $ toExprAtom nea

instance ToExpr NumExpr1 where
  toExpr ne =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    toExpr1 ne

toExprAtom :: NumExprAtom -> ExprAtom
toExprAtom (NumExprAtom neah eat as) =
  ExprAtom (toExprAtomHead neah) eat as

instance ToExpr NumExprAtom where
  toExpr nea =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom $ toExprAtom nea

toExprAtomHead :: NumExprAtomHead -> ExprAtomHead
toExprAtomHead (NBuiltinNumUnOp bnuo nea) =
  EBuiltinUnOp (BBuiltinNumUnOp bnuo) (toExprAtom nea)
toExprAtomHead (NNumExpr ne) = EExpr $ toExpr ne
toExprAtomHead (NIdentOrQuotedOp ioqo) = EIdentOrQuotedOp ioqo
toExprAtomHead (NIntLiteral il) = EIntLiteral il
toExprAtomHead (NFloatLiteral fl) = EFloatLiteral fl
toExprAtomHead (NIfThenElseExpr itee) = EIfThenElseExpr itee
toExprAtomHead (NLetExpr le) = ELetExpr le
toExprAtomHead (NCallExpr ce) = ECallExpr ce
toExprAtomHead (NGenCallExpr gce) = EGenCallExpr gce

instance ToExpr NumExprAtomHead where
  toExpr neah =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (toExprAtomHead neah)
                EATNothing
                (Annotations []))

instance ToExpr BoolLiteral where
  toExpr bl = toExpr $ EBoolLiteral bl

instance ToExpr IntLiteral where
  toExpr il = toExpr $ EIntLiteral il

instance ToExpr SetLiteral where
  toExpr sl =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (ESetLiteral sl)
                EATNothing
                (Annotations []))

instance ToExpr SetComp where
  toExpr sc =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (ESetComp sc)
                EATNothing
                (Annotations []))

instance ToExpr ArrayLiteral where
  toExpr al =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (EArrayLiteral al)
                EATNothing
                (Annotations []))

instance ToExpr ArrayComp where
  toExpr ac =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (EArrayComp ac)
                EATNothing
                (Annotations []))

instance ToExpr IfThenElseExpr where
  toExpr itee =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (EIfThenElseExpr itee)
                EATNothing
                (Annotations []))

instance ToExpr CallExpr where
  toExpr ce =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (ECallExpr ce)
                EATNothing
                (Annotations []))

instance ToExpr LetExpr where
  toExpr le =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (ELetExpr le)
                EATNothing
                (Annotations []))

instance ToExpr GenCallExpr where -- TODO: LOCALS!!
  toExpr gce =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (EGenCallExpr gce)
                EATNothing
                (Annotations []))

instance ToExpr Ident where
  toExpr i =
    Expr $ EExpr11 $ EExpr10 $ EExpr9 $ EExpr8 $ EExpr7 $
    EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 $
    EExprAtom (ExprAtom
                (EIdentOrQuotedOp (IIdent i))
                EATNothing
                (Annotations []))

instance ToExpr IdentOrQuotedOp where
  toExpr (IIdent i) = toExpr i
