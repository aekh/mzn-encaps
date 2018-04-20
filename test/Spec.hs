import Test.QuickCheck
--import Test.HUnit
--import Test.Framework
--import Test.Framework.Providers.HUnit
import Data.Monoid
import Control.Monad
--import Utils
import Data.List ((\\))

import Debug.Trace

--pushTest :: Assertion
--pushTest = [NumLit 1] ^? push (NumLit 1)

--pushPopTest :: Assertion
--pushPopTest = [] ^? (push (NumLit 0) >> void pop)

--main :: IO ()
--main = defaultMainWithOpts
--       [testCase "push" pushTest
--       ,testCase "push-pop" pushPopTest]
--       mempty
import Translator
import CST
import CST.Utils
import FMD
import FMD.Extra
import Encapsulator.Ranker
import Encapsulator.Common

takeFirstConstraintExpr :: CST -> Expr
takeFirstConstraintExpr (Model (IConstraintItem (ConstraintItem e):_)) = e
takeFirstConstraintExpr (Model (_:is)) = takeFirstConstraintExpr $ Model is
takeFirstConstraintExpr (Model []) = error "Error: no constraints"

main :: IO ()
main = do
  --quickCheck prop_translator
  putStrLn "\ntest_identifiers"
  quickCheck test_identifiers

  putStrLn "\ntest_toType*"
  quickCheck test_toType1
  quickCheck test_toType2
  quickCheck test_toType3

  putStrLn "\ntest_isVar*"
  quickCheck test_isVar1
  quickCheck test_isVar2
  quickCheck test_isVar3

  putStrLn "\ntest_stripArrayType "
  quickCheck test_stripArrayType

  putStrLn "\ntest_argumentModesty*"
  quickCheck test_argumentModesty1
  quickCheck test_argumentModesty2
  quickCheck test_argumentModesty3
  quickCheck test_argumentModesty4
  quickCheck test_argumentModesty5

  putStrLn "\ntest_localVariable*"
  quickCheck test_localVariable1
  quickCheck test_localVariable2
  quickCheck test_localVariable3
  quickCheck test_localVariable4
  quickCheck test_localVariable5

  putStrLn "\ntest_argumentSignificance*"
  quickCheck test_argumentSignificance1
  quickCheck test_argumentSignificance2
  quickCheck test_argumentSignificance3
  quickCheck test_argumentSignificance4

  putStrLn "\ntest_objectiveFunction*"
  quickCheck test_objectiveFunction1
  quickCheck test_objectiveFunction2
  quickCheck test_objectiveFunction3

  putStrLn "\ntest_multiEncapsulation*"
  quickCheck test_multiEncapsulation1
  quickCheck test_multiEncapsulation2
  quickCheck test_multiEncapsulation3
  quickCheck test_multiEncapsulation4

  putStrLn "\ntest_multiEncapsulation*"
  quickCheck test_solutionModesty1
  quickCheck test_solutionModesty2
  quickCheck test_solutionModesty3
  quickCheck test_solutionModesty4
  quickCheck test_solutionModesty5
  quickCheck test_solutionModesty6

  putStrLn "\nnormalise"
  quickCheck test_normalise

prop_translator cst = parseString (show cst) == Right cst
  where types = cst :: CST

test_identifiers = identifiers expr == expected
  where Right cst = parseString
          "int: i;\
          \int: k;\
          \array [1..k,1..k] of var int: X;\
          \array [1..i,1..k] of var int: Y;\
          \var int: x;\
          \var int: y;\
          \var int: z;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = toExpr
          (ELt (toExpr7 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))
                 (toExpr7 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations [])))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "x"), toExpr (Ident "y")]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int), toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        toExpr7 x = EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 x
        sameElems x y = null (x \\ y) && null (y \\ x)
        expected = Ident <$> ["X","x","y"]


test_toType1 = toType expr env [] == expected
  where Right cst = parseString "var int: x; solve satisfy;"
        env = mkEnv cst
        expr = toExpr $ Ident "x"
        expected = BaseTiExpr Var BInt

test_toType2 = toType expr env [] == expected
  where Right cst = parseString "array [1..10] of var int: x; solve satisfy;"
        env = mkEnv cst
        expr = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        expected = BaseTiExpr Var BInt

test_toType3 = toType expr env [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x; 1..10: k; solve satisfy;"
        env = mkEnv cst
        expr = toExpr
          (EPlus (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))))
                 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations []))))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "k")]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        expected = BaseTiExpr Var BInt

test_isVar1 = isVar expr env [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x; solve satisfy;"
        env = mkEnv cst
        expr = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        expected = True

test_isVar2 = isVar expr env [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x; 1..10: k; solve satisfy;"
        env = mkEnv cst
        expr = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "k")]) EATNothing)
                   (Annotations [])
        expected = True

test_isVar3 = isVar expr env [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x; 1..10: k; solve satisfy;"
        env = mkEnv cst
        expr = toExpr
          (EPlus (EExpr3 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))))
                 (EExpr2 (EExpr1 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations []))))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "k")]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        expected = True

test_stripArrayType = stripArrayType bte eat env [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x; solve satisfy;"
        env = mkEnv cst
        bte = BaseTiExpr Par (BArrayTiExprTail (ArrayTiExprTail tes te))
        tes = [TiExpr (BaseTiExpr Par (BRange (toNumExpr (toExpr (1::Int))) (toNumExpr (toExpr (10::Int)))))]
        te = TiExpr (BaseTiExpr Var BInt)
        eat = ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing
        expected = BaseTiExpr Var BInt

test_argumentModesty1 = argumentModesty expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \var int: y;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = Expr (EEquivalence e1 e2)
        Expr e1 = toExpr (Ident "x")
        Expr (EExpr11 e2) = toExpr (Ident "y")
        expected = Score (2,2)

test_argumentModesty2 = argumentModesty expr fmd [] == expected
  where Right cst = parseString
          "array [1..5] of var int: x;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = toExpr
          (ELt (toExpr7 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))
                 (toExpr7 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations [])))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (2::Int)]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        toExpr7 x = EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 x
        expected = Score (5,5)


test_argumentModesty3 = argumentModesty expr fmd [] == expected
  where Right cst = parseString
          "array [1..10] of var int: x;\
          \int: i;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = toExpr
          (ELt (toExpr7 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))
                 (toExpr7 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations [])))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "i")]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "x")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        toExpr7 x = EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 x
        expected = Score (11,11)

test_argumentModesty4 = argumentModesty expr fmd [] == expected
  where Right cst = parseString
          "int: k;\
          \array [1..k] of var int: X;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = toExpr
          (ELt (toExpr7 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))
                 (toExpr7 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations [])))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (2::Int)]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        toExpr7 x = EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 x
        expected = Score (0,int_max)

test_argumentModesty5 = argumentModesty expr fmd [] == expected
  where Right cst = parseString
          "int: k;\
          \array [1..k,1..k] of var int: X;\
          \var int: y;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = toExpr
          (ELt (toExpr7 (EExprAtom (ExprAtom (EExpr expr1) EATNothing (Annotations []))))
                 (toExpr7 (EExprAtom (ExprAtom (EExpr expr2) EATNothing (Annotations [])))))
        expr1 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (Ident "y"), toExpr (Ident "y")]) EATNothing)
                   (Annotations [])
        expr2 = toExpr $
          ExprAtom (EIdentOrQuotedOp (IIdent (Ident "X")))
                   (ExprAtomTail (ArrayAccessTail [toExpr (1::Int), toExpr (1::Int)]) EATNothing)
                   (Annotations [])
        toExpr7 x = EExpr6 $ EExpr5 $ EExpr4 $ EExpr3 $ EExpr2 $ EExpr1 x
        expected = Score (1,(int_max^2)+1)

test_localVariable1 = localVariable expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \var int: y;\
          \constraint x == y;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (0,0)

test_localVariable2 = localVariable expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \var int: y;\
          \constraint let {int: k = 5; var int: a; constraint a < 100;} in x == y \\/ x*k == a;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (1,1)

test_localVariable3 = localVariable expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \var int: y;\
          \constraint let {int: k = 5; var int: a; constraint let {var int: b; constraint b <= x /\\ b >= y;} in a*b = k;} in a+x == y \\/ a-y == k*x;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (2,2)

test_localVariable4 = localVariable expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \var int: y;\
          \constraint let {array [1..10] of var int: A; constraint forall(i in 1..10)(A[i] < x - i);} in exists(i in 1..10)(i*y == x+i);\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (10,10)

test_localVariable5 = localVariable expr fmd [] == expected
  where Right cst = parseString
          "-500..500: k;\
          \var int: y;\
          \constraint let {array [1..k] of var int: A; var int: x; constraint forall(i in 1..k)(A[i] < x - i);} in exists(i in 1..10)(i*y == x+i);\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (1,501)

test_argumentSignificance1 = argumentSignificance expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \-128..256: k;\
          \constraint x == k;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (0,0)

test_argumentSignificance2 = argumentSignificance expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \-128..256: k;\
          \constraint x == k \\/ x == k - 10;\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (200,200)

test_argumentSignificance3 = argumentSignificance expr fmd [] == expected
  where Right cst = parseString
          "1..10: k;\
          \array [1..k] of var int: x;\
          \constraint forall(i in 1..k-1)(x[i] <= x[i+1]);\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (0,80)

test_argumentSignificance4 = argumentSignificance expr fmd [] == expected
  where Right cst = parseString
          "int: k;\
          \array [1..k] of var int: x;\
          \constraint forall(i in 1..k-1)(x[i] <= x[i+1]);\
          \solve satisfy;"
        env = mkEnv cst
        fmd = FMD env [] []
        expr = takeFirstConstraintExpr cst
        expected = Score (0,99)

test_objectiveFunction1 = objectiveFunction expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \constraint x <= 1;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (1,1)

test_objectiveFunction2 = objectiveFunction expr' fmd [] == expected
  where Right cst = parseString
          "2..10: k;\
          \var int: x;\
          \var int: y;\
          \solve minimize x+y;"
        Right cst1 = parseString "constraint forall(i in 1..k)(x <= 1);"
        Right cst1' = parseString "constraint x <= 1;"
        Right cst2 = parseString "constraint true in {y <= 1 | i in 1..k};"
        Right cst2' = parseString "constraint y <= 1;"
        Right cst' = parseString "constraint AbV_0 <= 1;"
        env = insertAbstr (Abstr (toExpr $ Ident "x") (Ident "AbV_0")) $
              insertAbstr (Abstr (toExpr $ Ident "y") (Ident "AbV_0")) $
              mkEnv cst
        fmd = FMD env vs es
        vs = [Vertex expr1, Vertex expr1', Vertex expr2, Vertex expr2'
             ,Vertex expr']
        es = [Edge Subformula 0 1, Edge Subformula 2 3
             ,Edge Abstraction 1 4, Edge Abstraction 3 4]
        expr1 = takeFirstConstraintExpr cst1
        expr1' = takeFirstConstraintExpr cst1'
        expr2 = takeFirstConstraintExpr cst2
        expr2' = takeFirstConstraintExpr cst2'
        expr' = takeFirstConstraintExpr cst'
        expected = Score (2,2)

test_objectiveFunction3 = objectiveFunction expr fmd [] == expected
  where Right cst = parseString
          "int: k;\
          \var int: x;\
          \constraint x <= k;\
          \solve maximize x-k;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (1,1)

test_multiEncapsulation1 = multiEncapsulation expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \constraint x <= 1;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (1,1)

test_multiEncapsulation2 = multiEncapsulation expr' fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \constraint forall(i in 1..10)(x <= 1);\
          \solve maximize x;"
        Right cst' = parseString "constraint x <= 1;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr, Vertex expr'] [Edge Subformula 0 1]
        expr = takeFirstConstraintExpr cst
        expr' = takeFirstConstraintExpr cst'
        expected = Score (10,10)

test_multiEncapsulation3 = multiEncapsulation expr' fmd [] == expected
  where Right cst = parseString
          "int: k;\
          \var int: x;\
          \constraint forall([x <= k -> x <= 1 | i in 1..k]);\
          \solve satisfy;"
        Right cst' = parseString "constraint x <= 1;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr, Vertex expr'] [Edge Subformula 0 1]
        expr = takeFirstConstraintExpr cst
        expr' = takeFirstConstraintExpr cst'
        expected = Score (0,int_max)

test_multiEncapsulation4 = multiEncapsulation expr' fmd [] == expected
  where Right cst = parseString
          "2..10: k;\
          \var int: x;\
          \var int: y;\
          \solve maximize x;"
        Right cst1 = parseString "constraint forall(i in 1..k)(x <= 1);"
        Right cst1' = parseString "constraint x <= 1;"
        Right cst2 = parseString "constraint forall([y <= 1 | i in 1..k]);"
        Right cst2' = parseString "constraint y <= 1;"
        Right cst' = parseString "constraint AbV_0 <= 1;"
        env = insertAbstr (Abstr (toExpr $ Ident "x") (Ident "AbV_0")) $
              insertAbstr (Abstr (toExpr $ Ident "y") (Ident "AbV_0")) $
              mkEnv cst
        fmd = FMD env vs es
        vs = [Vertex expr1, Vertex expr1', Vertex expr2, Vertex expr2'
             ,Vertex expr']
        es = [Edge Subformula 0 1, Edge Subformula 2 3
             ,Edge Abstraction 1 4, Edge Abstraction 3 4]
        expr1 = takeFirstConstraintExpr cst1
        expr1' = takeFirstConstraintExpr cst1'
        expr2 = takeFirstConstraintExpr cst2
        expr2' = takeFirstConstraintExpr cst2'
        expr' = takeFirstConstraintExpr cst'
        expected = Score (4,20)

test_solutionModesty1 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "var int: x;\
          \constraint x <= 1;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (int_max, int_max)

test_solutionModesty2 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "var set of {1,2,3}: x;\
          \constraint 1 in x;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (2, 2^3)

test_solutionModesty3 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "2..10: k;\
          \var set of 1..k: x;\
          \constraint 1 in x;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (2^2, 2^10)

test_solutionModesty4 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "3..50: k;\
          \var set of 1..k: x;\
          \var 1..100: y;\
          \constraint y in x;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (2^3 * 100, 2^31 * 100)

test_solutionModesty5 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "3..50: k;\
          \array [1..k] of var set of 1..k: x;\
          \var 1..k: y;\
          \constraint y in x;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score ((2^3)^3 * 3, (2^31)^31 * 50)

test_solutionModesty6 = solutionModesty expr fmd [] == expected
  where Right cst = parseString
          "1..10: k;\
          \array [1..k] of set of {1,2,3}: x;\
          \constraint 3 >= x;\
          \solve maximize x;"
        env = mkEnv cst
        fmd = FMD env [Vertex expr] []
        expr = takeFirstConstraintExpr cst
        expected = Score (2, (2^3)^10)

test_normalise = normalise list == expected
  where list = [Score (0,1)
               ,Score (2,3)
               ,Score (4,6)]
        expected = [Score (0,1666666666666666)
                   ,Score (3333333333333333,5000000000000000)
                   ,Score (6666666666666666,10000000000000000)]
