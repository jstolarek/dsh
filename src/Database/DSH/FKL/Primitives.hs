{-# LANGUAGE TemplateHaskell #-}

-- | Smart constructors for FKL functions and operators
module Database.DSH.FKL.Primitives where

import           Prelude                    hiding (concat, fst, snd)

import           Text.Printf

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang
import           Database.DSH.Impossible

--------------------------------------------------------------------------------
-- Smart constructors for primitive combinators in the lifting FKL dialect

-- tranpose :: [[a]] -> [[a]]
transpose :: LExpr -> Nat -> LExpr
transpose e d =
    let t = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d t) (LiftedN d Transpose) e

-- transpose :: [a] -> [[a]]
reshape :: Integer -> LExpr -> Nat -> LExpr
reshape n e d =
    let t = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d $ ListT t) (LiftedN d $ Reshape n) e

-- group :: [a] -> [b] -> [(a, [b])]
group :: LExpr -> LExpr -> Nat -> LExpr
group gs xs d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT gt = unliftTypeN d $ typeOf gs
        rt             = listT (pairT gt (listT xt))
    in PApp2 (liftTypeN d rt) (LiftedN d Group) gs xs

-- sort :: [a] -> [b] -> [b]
sort :: LExpr -> LExpr -> Nat -> LExpr
sort ss xs d =
    let xst = unliftTypeN d $ typeOf xs
    in PApp2 (liftTypeN d xst) (LiftedN d Sort) ss xs

cons :: LExpr -> LExpr -> Nat -> LExpr
cons e1 e2 d =
    let t2 = unliftTypeN d $ typeOf e2
    in PApp2 (liftTypeN d t2) (LiftedN d Cons) e1 e2

pair :: LExpr -> LExpr -> Nat -> LExpr
pair e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
        t2 = unliftTypeN d $ typeOf e2
        rt = pairT t1 t2
    in PApp2 (liftTypeN d rt) (LiftedN d Pair) e1 e2

-- zip :: [a] -> [b] -> [(a, b)]
zip :: LExpr -> LExpr -> Nat -> LExpr
zip xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
    in PApp2 (liftTypeN d $ listT (pairT xt yt)) (LiftedN d Zip) xs ys

cartProduct :: LExpr -> LExpr -> Nat -> LExpr
cartProduct xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = typeOf ys
    in PApp2 (liftTypeN d $ listT (pairT xt yt)) (LiftedN d CartProduct) xs ys

-- nestProduct :: [a] -> [b] -> [(a, [(a, b)])]
nestProduct :: LExpr -> LExpr -> Nat -> LExpr
nestProduct xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
        rt       = listT (pairT xt (listT (pairT xt yt)))
    in PApp2 (liftTypeN d rt) (LiftedN d NestProduct) xs ys

thetaJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> Nat -> LExpr
thetaJoin p xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
    in PApp2 (liftTypeN d $ listT (pairT xt yt)) (LiftedN d $ ThetaJoin p) xs ys

nestJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> Nat -> LExpr
nestJoin p xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
        rt       = listT (pairT xt (listT (pairT xt yt)))
    in PApp2 (liftTypeN d rt) (LiftedN d $ NestJoin p) xs ys

semiJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> Nat -> LExpr
semiJoin p e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) (LiftedN d $ SemiJoin p) e1 e2

antiJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> Nat -> LExpr
antiJoin p e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) (LiftedN d $ AntiJoin p) e1 e2

append :: LExpr -> LExpr -> Nat -> LExpr
append e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) (LiftedN d Append) e1 e2

index :: LExpr -> LExpr -> Nat -> LExpr
index e1 e2 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t) (LiftedN d Index) e1 e2

length :: LExpr -> Nat -> LExpr
length e1 d = PApp1 (liftTypeN d intT) (LiftedN d Length) e1

-- FIXME this is not the right place to perform this step. If at all,
-- do it during compilation to VL.
head :: LExpr -> Nat -> LExpr
head = the

the :: LExpr -> Nat -> LExpr
the e1 d =
    let ListT t1 = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d The) e1

last :: LExpr -> Nat -> LExpr
last e1 d =
    let ListT t1 = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d Last) e1

tail :: LExpr -> Nat -> LExpr
tail e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d Tail) e1

nub :: LExpr -> Nat -> LExpr
nub e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d Nub) e1

number :: LExpr -> Nat -> LExpr
number e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
        rt      = (ListT (PairT t IntT ))
    in PApp1 (liftTypeN d rt) (LiftedN d Number) e1

init :: LExpr -> Nat -> LExpr
init e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d Init) e1

reverse :: LExpr -> Nat -> LExpr
reverse e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) (LiftedN d Reverse) e1

and :: LExpr -> Nat -> LExpr
and e1 d = PApp1 (liftTypeN d BoolT) (LiftedN d And) e1

or :: LExpr -> Nat -> LExpr
or e1 d = PApp1 (liftTypeN d BoolT) (LiftedN d Or) e1

sum :: LExpr -> Nat -> LExpr
sum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (LiftedN d Sum) e1

avg :: LExpr -> Nat -> LExpr
avg e1 d = PApp1 (liftTypeN d DoubleT) (LiftedN d Avg) e1

minimum :: LExpr -> Nat -> LExpr
minimum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (LiftedN d Minimum) e1

maximum :: LExpr -> Nat -> LExpr
maximum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (LiftedN d Maximum) e1

concat :: LExpr -> Nat -> LExpr
concat e d =
    let ListT rt@(ListT _) = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d rt) (LiftedN d Concat) e

dist :: LExpr -> LExpr -> LExpr
dist e1 e2 =
    let t1 = typeOf e1
    in PApp2 (listT t1) (LiftedN Zero Dist) e1 e2

distL :: LExpr -> LExpr -> LExpr
distL e1 e2 =
    let t1 = typeOf e1
    in PApp2 (listT t1) (LiftedN (Succ Zero) Dist) e1 e2

restrict :: LExpr -> LExpr -> Nat -> LExpr
restrict xs bs d =
    let xst = unliftTypeN d $ typeOf xs
    in PApp2 (liftTypeN d xst) (LiftedN d Restrict) xs bs

-- combine :: [Bool] -> [a] -> [a] -> [a]
combine :: LExpr -> LExpr -> LExpr -> Nat -> LExpr
combine e1 e2 e3 d =
    let xst = unliftTypeN d $ typeOf e2
    in PApp3 (liftTypeN d xst) (LiftedN d Combine) e1 e2 e3

fst :: LExpr -> Nat -> LExpr
fst e d =
    let PairT t1 _ = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d t1) (LiftedN d Fst) e

snd :: LExpr -> Nat -> LExpr
snd e d =
    let PairT _ t2 = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d t2) (LiftedN d Snd) e

--------------------------------------------------------------------------------
-- Smart constructors for binary and unary operators.

-- FIXME typing of binary operators is not correct
bin :: Type -> ScalarBinOp -> LExpr -> LExpr -> Nat -> LExpr
bin t o e1 e2 d = BinOp (liftTypeN d t) (LiftedN d o) e1 e2

un :: Type -> ScalarUnOp -> LExpr -> Nat -> LExpr
un t o e d = UnOp (liftTypeN d t) (LiftedN d o) e


--------------------------------------------------------------------------------
-- Smart constructors for special forms in both FKL dialects

qconcat :: Nat -> Expr l -> Expr l
qconcat n xs =
    let xst = typeOf xs
    in QConcat n (unwrapListType n xst) xs

  where
    unwrapListType :: Nat -> Type -> Type
    unwrapListType Zero t               = t
    unwrapListType (Succ n') (ListT xt) = unwrapListType n' xt
    unwrapListType _         _          = $impossible

unconcat :: Nat -> Expr l -> Expr l -> Expr l
unconcat n shape bottom = UnConcat n (wrapListType n bt) shape bottom
  where
    bt = typeOf bottom

    wrapListType :: Nat -> Type -> Type
    wrapListType Zero t     = t
    wrapListType (Succ n') t = wrapListType n' (listT t)

if_ :: LExpr -> LExpr -> LExpr -> LExpr
if_ eb et ee =
    let (BoolT, tt, te) = (typeOf eb, typeOf et, typeOf ee)
    in if tt == te
       then If tt eb et ee
       else error $ printf "FKL.if: incompatible types: %s %s" (pp tt) (pp te)

let_ :: Ident -> Expr l -> Expr l -> Expr l
let_ x e1 e2 = Let (typeOf e2) x e1 e2
