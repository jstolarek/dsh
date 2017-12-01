{-# LANGUAGE GADTs                #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeFamilyDependencies         #-}
{-# LANGUAGE MultiParamTypeClasses         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Database.DSH.Provenance.Lineage
    ( -- * Lineage transformation and data type
      lineage, Lineage, QLT(..)

      -- * Accessing data and provenance components of lineage-annotated value
    , lineageDataQ, lineageProvQ, emptyLineageQ
    ) where

import           Data.Decimal
import           Data.Proxy
import           Data.Text
import           Data.Time.Calendar               (Day)
import qualified Data.Traversable as T
import           Data.Typeable
import           Data.Scientific
import qualified Data.Sequence as S
import qualified Data.Set      as Set

import           Database.DSH.Common.CompileM
import           Database.DSH.Common.Impossible
import           Database.DSH.Frontend.Externals ()
import           Database.DSH.Frontend.Internals
import           Database.DSH.Frontend.TH
import           Database.DSH.Frontend.TupleTypes

import           Data.Type.Equality

--------------------------------------------------------------------------------
--                           LINEAGE DATA TYPES                               --
--------------------------------------------------------------------------------

data LineageAnnotEntry key = LineageAnnotEntry Text key deriving (Eq, Ord)

instance Show key => Show (LineageAnnotEntry key) where
    show (LineageAnnotEntry t k) = "( " ++ show t ++ ", " ++ show k ++ " )"

deriveQA   ''LineageAnnotEntry
deriveView ''LineageAnnotEntry

newtype LineageAnnot key = LineageAnnot (Set.Set (LineageAnnotEntry key))

instance Show key => Show (LineageAnnot key) where
    show (LineageAnnot laes) = show (Set.toList laes)

-- Instance written by hand because we need extra Ord constraint
instance (QA key, Ord key) => QA (LineageAnnot key) where
    type Rep (LineageAnnot key) = Rep [LineageAnnotEntry key]
    toExp (LineageAnnot es) = toExp (Set.toList es)
    frExp as = LineageAnnot (Set.fromList (frExp as))

data Lineage a k where
    Lineage :: a -> LineageAnnot k -> Lineage a k

instance TA (Lineage a k)

instance (Show a, Show k) => Show (Lineage a k) where
    show (Lineage d l) = "( data = "    ++ show d ++
                         ", lineage = " ++ show l ++ " )"

-- Instance written by hand because we need extra Ord constraint
instance (QA a, QA k, Ord k) => QA (Lineage a k) where
    type Rep (Lineage a k) = (Rep a, Rep (LineageAnnot k))
    toExp (Lineage a k)    = TupleConstE ((Tuple2E (toExp a)) (toExp k))
    frExp (TupleConstE (Tuple2E a k)) = Lineage (frExp a) (frExp k)
    frExp _ = $impossible

deriveView ''Lineage

--------------------------------------------------------------------------------
--                        LINEAGE TRANSFORMATION                              --
--------------------------------------------------------------------------------

-- | Type of row annotated with lineage
type LineageE a k = (a, LineageAnnotE k)

type LineageAnnotE k = [(Text, k)]

type family LineageTransform a k = r | r -> a where
    LineageTransform ()         t =  ()
    LineageTransform Bool       t =  Bool
    LineageTransform Char       t =  Char
    LineageTransform Integer    t =  Integer
    LineageTransform Double     t =  Double
    LineageTransform Text       t =  Text
    LineageTransform Decimal    t =  Decimal
    LineageTransform Scientific t =  Scientific
    LineageTransform Day        t =  Day
    LineageTransform [a]        t = [LineageE (LineageTransform a t) t]
    LineageTransform (a,b) t =
        $(mkLineageTransformTupleRHS [''a, ''b] ''t)
    LineageTransform (a,b,c) t =
        $(mkLineageTransformTupleRHS [''a, ''b, ''c] ''t)
    LineageTransform (a,b,c,d) t =
        $(mkLineageTransformTupleRHS [''a, ''b, ''c, ''d] ''t)
    LineageTransform (a,b,c,d,e) t =
        $(mkLineageTransformTupleRHS [''a, ''b, ''c, ''d, ''e] ''t)
    LineageTransform (a,b,c,d,e,f) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f] ''t)
    LineageTransform (a,b,c,d,e,f,g) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g] ''t)
    LineageTransform (a,b,c,d,e,f,g,h) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h]
                                     ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k,l) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k, ''l] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k,l,m) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k, ''l, ''m] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k,l,m,n) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k, ''l, ''m, ''n] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k, ''l, ''m, ''n, ''o] ''t)
    LineageTransform (a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p) t =
        $(mkLineageTransformTupleRHS [ ''a, ''b, ''c, ''d, ''e, ''f, ''g, ''h
                                     , ''i, ''j, ''k, ''l, ''m, ''n, ''o, ''p]
          ''t)

class (QA a) => QLT a where
    type family LT a k
    ltEq :: forall k. (QA k) => Proxy a -> Proxy k
         -> LineageTransform (Rep a) (Rep k) :~: Rep (LT a k)

instance QLT () where
    type LT () k = ()
    ltEq _ _ = Refl

instance QLT Bool where
    type LT Bool k = Bool
    ltEq _ _ = Refl

instance QLT Char where
    type LT Char k = Char
    ltEq _ _ = Refl

instance QLT Integer where
    type LT Integer k = Integer
    ltEq _ _ = Refl

instance QLT Double where
    type LT Double k = Double
    ltEq _ _ = Refl

instance QLT Text where
    type LT Text k = Text
    ltEq _ _ = Refl

instance QLT Decimal where
    type LT Decimal k = Decimal
    ltEq _ _ = Refl

instance QLT Scientific where
    type LT Scientific k = Scientific
    ltEq _ _ = Refl

instance QLT Day where
    type LT Day k = Day
    ltEq _ _ = Refl

instance QLT a => QLT [a] where
    type LT [a] k = [Lineage (LT a k) k]
    ltEq _ k = case ltEq (Proxy :: Proxy a) k of
                 Refl -> Refl

-- QLT instances for tuples
$(mkQLTTupleInstances 16)

-- | Perform lineage transformation on a query
lineage :: forall a k.
           ( Reify (Rep a), QA k, Typeable (Rep k), QLT a
           , Reify (LineageTransform (Rep a) (Rep k)) )
        => Proxy k -> Q a -> Q (LT a k)
lineage pk (Q a) =
   let pa = Proxy :: Proxy a
   in Q (castWith (apply Refl (ltEq pa pk))
                  (runLineage (lineageTransform mkReify
                                               (mkReify :: DReify (Rep k)) a)))

typeLT :: forall a k. Type a -> Type k -> Type (LineageTransform a k)
typeLT (UnitT)          _ = UnitT
typeLT (BoolT)          _ = BoolT
typeLT (CharT)          _ = CharT
typeLT (IntegerT)       _ = IntegerT
typeLT (DoubleT)        _ = DoubleT
typeLT (TextT)          _ = TextT
typeLT (DecimalT)       _ = DecimalT
typeLT (ScientificT)    _ = ScientificT
typeLT (DayT)           _ = DayT
typeLT (ArrowT _ _)     _ = $impossible
typeLT (ListT lt) kt =
    ListT (TupleT $ Tuple2T (typeLT lt kt)
                      (ListT (TupleT $ Tuple2T TextT kt)))
typeLT (TupleT t) k =
    let typeLTTuple :: TupleType a -> Type (LineageTransform a k)
        typeLTTuple = $(mkTypeLT 'k 16)
    in typeLTTuple t

reifyLT :: forall a k. DReify a -> DReify k -> DReify (LineageTransform a k)
reifyLT ra rb Proxy = typeLT (ra Proxy) (rb Proxy)

lineageTransform :: forall a k. Typeable k
                 => DReify a -> DReify k -> Exp a
                 -> Compile (Exp (LineageTransform a k))
lineageTransform reifyA reifyK tbl@(TableE (TableDB name _ _) keyProj) = do
  let -- We have to perform runtime type equality to check that type of lineage
      -- key specified in a call to `lineage` matches the type returned by
      -- `keyProj` function stored in `TableE` constructor.
      keyEquality :: forall k1 k2. (Typeable k1, Typeable k2)
                  => DReify k1 -> (Integer -> Exp k2) -> Maybe (k1 :~: k2)
      keyEquality _ _ = eqT
  case keyEquality reifyK keyProj of
    Just Refl -> do
      let lam :: DReify b -> Integer -> Exp (LineageE b k)
          lam dreify a = lineageE (VarE dreify a)
                     (lineageAnnotE reifyK (pack name) (keyProj a :: Exp k))
          reifyC Proxy = case reifyA Proxy of
                           ListT t -> t
                           _       -> $impossible
      return (AppE Map (TupleConstE (Tuple2E
                        (LamE reifyC (lam (reifyLT mkReify reifyK))) tbl)))
    Nothing -> error "Type of table key does not match type of lineage key"

lineageTransform reifyA reifyK (AppE Map
                   (TupleConstE (Tuple2E (LamE reifyC lam) tbl))) = do
  -- translate the comprehension generator
  let reifyCs Proxy = ListT (reifyC Proxy)
  tbl' <- lineageTransform reifyCs reifyK tbl

  -- saturate the lambda and translate the resulting expression
  let reifyB Proxy = case reifyA Proxy of
                       ListT t -> t
                       _       -> $impossible
  boundVar <- freshVar
  bodyExp  <- lineageTransform reifyA reifyK (singletonE reifyB (lam boundVar))

  let lineageRecTy :: Type c -> Type (LineageTransform c k)
      lineageRecTy t = typeLT t (reifyK Proxy)

      annotTy = ListT (TupleT $ Tuple2T TextT (reifyK Proxy))

      reifyTy Proxy = case reifyA Proxy of
                        ListT t -> TupleT (Tuple2T (lineageRecTy t) annotTy)
                        _       -> $impossible

      reifyTy' Proxy = case reifyA Proxy of
                        ListT t -> lineageRecTy t
                        _       -> $impossible

      reifyTy'' Proxy = case reifyC Proxy of
                        t -> TupleT (Tuple2T (lineageRecTy t) annotTy)

      -- lambda that appends lineages
      lamAppend al z =
             lineageE (lineageDataE (VarE reifyTy z))
                        ((lineageProvE (VarE reifyTy al)) `lineageAppendE`
                         (lineageProvE (VarE reifyTy  z)))

      -- comprehension that appends lineages of currently traversed collection
      -- and result of nested part of comprehension
      compLineageApp al = AppE Map (TupleConstE
             (Tuple2E (LamE reifyTy (lamAppend al)) bodyExp))

      -- comprehension over singleton list containing data originally assigned
      -- to comprehension binder
      compSingOrg al = AppE ConcatMap (TupleConstE
             (Tuple2E (LamE reifyTy'
                            (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE reifyTy' (lineageDataE
                                   (VarE reifyTy al)))))
  return (AppE ConcatMap (TupleConstE (Tuple2E
                                       (LamE reifyTy'' compSingOrg) tbl')))

lineageTransform reifyA reifyK (AppE ConcatMap
                   (TupleConstE (Tuple2E (LamE reifyC lam) tbl))) = do
  -- translate the comprehension generator
  let reifyCs Proxy = ListT (reifyC Proxy)
  tbl' <- lineageTransform reifyCs reifyK tbl

  -- saturate the lambda and translate the resulting expression
  boundVar <- freshVar
  bodyExp  <- lineageTransform reifyA reifyK (lam boundVar)

  let lineageRecTy :: Type c -> Type (LineageTransform c k)
      lineageRecTy t = typeLT t (reifyK Proxy)

      annotTy = ListT (TupleT $ Tuple2T TextT (reifyK Proxy))

      reifyTy Proxy = case reifyA Proxy of
                        ListT t -> TupleT (Tuple2T (lineageRecTy t) annotTy)
                        _       -> $impossible

      reifyTy' Proxy = case reifyA Proxy of
                        ListT t -> lineageRecTy t
                        _       -> $impossible

      reifyTy'' Proxy = case reifyC Proxy of
                        t -> TupleT (Tuple2T (lineageRecTy t) annotTy)

      -- lambda that appends lineages
      lamAppend al z =
             lineageE (lineageDataE (VarE reifyTy z))
                        ((lineageProvE (VarE reifyTy al)) `lineageAppendE`
                         (lineageProvE (VarE reifyTy  z)))

      -- comprehension that appends lineages of currently traversed collection
      -- and result of nested part of comprehension
      compLineageApp al = AppE Map (TupleConstE
             (Tuple2E (LamE reifyTy (lamAppend al)) bodyExp))

      -- comprehension over singleton list containing data originally assigned
      -- to comprehension binder
      compSingOrg al = AppE ConcatMap (TupleConstE
             (Tuple2E (LamE reifyTy'
                            (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE reifyTy' (lineageDataE
                                   (VarE reifyTy al)))))
      -- JSTOLAREK: alternative version using let-bindings.  These currently
      -- don't work.  See email from Alex on 10/07/2017
{-
      compSingOrg al = LetE boundVar (lineageDataE (VarE reifyTy al))
                                     (compLineageApp al)
-}

  return (AppE ConcatMap (TupleConstE (Tuple2E
                                       (LamE reifyTy'' compSingOrg) tbl')))

-- L(xs ++ ys) = L(xs) ++ L(ys)
lineageTransform reifyA reifyK (AppE Append (TupleConstE (Tuple2E xs ys))) =
    do xs' <- lineageTransform reifyA reifyK xs
       ys' <- lineageTransform reifyA reifyK ys
       return (AppE Append (TupleConstE (Tuple2E xs' ys')))

-- L(reverse xs) = reverse (L(xs))
lineageTransform reifyA reifyK (AppE Reverse xs) = do
  xs' <- lineageTransform reifyA reifyK  xs
  return (AppE Reverse xs')

-- zip
lineageTransform reifyA reifyK (AppE Zip (TupleConstE (Tuple2E xs ys))) = do
  let reifyFst Proxy = case reifyA Proxy of
                         ListT (TupleT (Tuple2T t _)) -> ListT t
                         _ -> $impossible

      reifySnd Proxy = case reifyA Proxy of
                         ListT (TupleT (Tuple2T _ t)) -> ListT t
                         _ -> $impossible

      annotTy = ListT (TupleT $ Tuple2T TextT (reifyK Proxy))

      lineageRecTy :: Type c -> Type (LineageTransform c k)
      lineageRecTy t = typeLT t (reifyK Proxy)

  xs' <- lineageTransform reifyFst reifyK xs
  ys' <- lineageTransform reifySnd reifyK ys

  let -- zip (L(xs)) (L(ys))
      zipL = AppE Zip (TupleConstE (Tuple2E xs' ys'))

      reifyX Proxy = case reifyA Proxy of
          ListT (TupleT (Tuple2T t1 t2)) ->
              TupleT (Tuple2T (TupleT (Tuple2T (lineageRecTy t1) annotTy))
                              (TupleT (Tuple2T (lineageRecTy t2) annotTy)))
          _ -> $impossible

      -- (\x -> { data = ((fst x).data, (snd x).data)
      --        , prov = ((fst x).prov, (snd x).prov) })
      lam x = lineageE
              (TupleConstE (Tuple2E
                            (lineageDataE (AppE Fst (VarE reifyX x)))
                            (lineageDataE (AppE Snd (VarE reifyX x)))))
              (lineageProvE (AppE Fst (VarE reifyX x)) `lineageAppendE`
                            (lineageProvE (AppE Fst (VarE reifyX x))))

  return (AppE Map (TupleConstE (Tuple2E (LamE reifyX lam) zipL)))

-- variables
lineageTransform _ reifyK (VarE reifyVar v) = do
  let reifyVar' Proxy = typeLT (reifyVar Proxy) (reifyK Proxy)
  return (VarE reifyVar' v)

-- constants
lineageTransform _ _ e@(UnitE)         = return e
lineageTransform _ _ e@(BoolE       _) = return e
lineageTransform _ _ e@(CharE       _) = return e
lineageTransform _ _ e@(IntegerE    _) = return e
lineageTransform _ _ e@(DoubleE     _) = return e
lineageTransform _ _ e@(TextE       _) = return e
lineageTransform _ _ e@(DayE        _) = return e
lineageTransform _ _ e@(ScientificE _) = return e
lineageTransform _ _ e@(DecimalE    _) = return e

-- lists
lineageTransform _ reifyK (ListE reifyA xs) = do
  xs' <- T.mapM (lineageTransform reifyA reifyK) xs
  let reifyA' Proxy = typeLT (reifyA Proxy) (reifyK Proxy)
  return (emptyLineageListE reifyA' reifyK (ListE reifyA' xs'))

-- guards
lineageTransform _ reifyK e@(AppE Guard _) = do
    return (emptyLineageListE (\Proxy -> UnitT) reifyK e)

-- cons
lineageTransform reifyA reifyK (AppE Cons (TupleConstE (Tuple2E x xs))) = do
  let reifyX Proxy = case reifyA Proxy of
                       ListT t -> t
                       _       -> $impossible
  x'  <- lineageTransform reifyX reifyK x
  xs' <- lineageTransform reifyA reifyK xs
  return (AppE Cons (TupleConstE (Tuple2E (emptyLineageE reifyK x') xs')))

-- tuples
lineageTransform reifyA reifyK (TupleConstE tupleE) = do
   let lineageTransformTupleConst =
           $(mkLineageTransformTupleConst 'reifyA 'reifyK 16)
   lineageTransformTupleConst tupleE

lineageTransform reifyA reifyK (AppE (TupElem t) arg) = do
    let lineageTransformTupElem =
            $(mkLineageTransformTupElem 'reifyA 'reifyK 'arg 16)
    lineageTransformTupElem t

lineageTransform reifyA reifyK (AppE Fst a) = do
  let reifyTuple Proxy = TupleT (Tuple2T (reifyA Proxy) $impossible)
  a' <- lineageTransform reifyTuple reifyK a
  return (AppE Fst a')

lineageTransform reifyB reifyK (AppE Snd a) = do
  let reifyTuple Proxy = TupleT (Tuple2T $impossible (reifyB Proxy))
  a' <- lineageTransform reifyTuple reifyK a
  return (AppE Snd a')


-- NOT YET IMPLEMENTED

-- concatMap (\x. concatMap (\y. map (\z. (z.data)^(z.prov + x.prov)) L(f y)) [x.data]) L(xs)
--
-- L (filter f xs)
--
-- This produces a list of xs annotated with complete provenance:
--
-- (concatMap (\x. concatMap (\y. map (\z. (x.data)^(z.prov + x.prov)) L[f y]) [x.data]) L(xs))
--
-- filter (\x. only (map f [x.data])) L(xs)
--
-- James' translation
--
--   map (\(x,b). x) (filter (\(x,b). b)  (map (\x. (x, f(x.data))) L(xs)))
--
-- but this works only on paper. Again f(x.data) is not a valid expression
lineageTransform _ _ (AppE Filter           _) = $unimplemented

-- concat has type [[a]] -> [a].  According to our TF declaration if input is
-- [[a]] the return type is [L [a]], but we want [L a].
lineageTransform _ _ (AppE Concat           _) = $unimplemented

lineageTransform _ _ (AppE Sum              _) = $unimplemented
lineageTransform _ _ (AppE Avg              _) = $unimplemented
lineageTransform _ _ (AppE Maximum          _) = $unimplemented
lineageTransform _ _ (AppE Minimum          _) = $unimplemented
lineageTransform _ _ (AppE Nub              _) = $unimplemented
lineageTransform _ _ (AppE GroupWithKey     _) = $unimplemented
lineageTransform _ _ (AppE SortWith         _) = $unimplemented
lineageTransform _ _ (AppE Cond             _) = $unimplemented
lineageTransform _ _ (AppE Only             _) = $unimplemented
lineageTransform _ _ (AppE Length           _) = $unimplemented
lineageTransform _ _ (AppE Null             _) = $unimplemented
lineageTransform _ _ (AppE Number           _) = $unimplemented
lineageTransform _ _ (AppE Add              _) = $unimplemented
lineageTransform _ _ (AppE Mul              _) = $unimplemented
lineageTransform _ _ (AppE Sub              _) = $unimplemented
lineageTransform _ _ (AppE Div              _) = $unimplemented
lineageTransform _ _ (AppE Mod              _) = $unimplemented
lineageTransform _ _ (AppE Not              _) = $unimplemented
lineageTransform _ _ (AppE And              _) = $unimplemented
lineageTransform _ _ (AppE Or               _) = $unimplemented
lineageTransform _ _ (AppE IntegerToDouble  _) = $unimplemented
lineageTransform _ _ (AppE IntegerToDecimal _) = $unimplemented
lineageTransform _ _ (AppE Lt               _) = $unimplemented
lineageTransform _ _ (AppE Lte              _) = $unimplemented
lineageTransform _ _ (AppE Gt               _) = $unimplemented
lineageTransform _ _ (AppE Gte              _) = $unimplemented
lineageTransform _ _ (AppE Equ              _) = $unimplemented
lineageTransform _ _ (AppE NEq              _) = $unimplemented
lineageTransform _ _ (AppE Conj             _) = $unimplemented
lineageTransform _ _ (AppE Disj             _) = $unimplemented
lineageTransform _ _ (AppE Like             _) = $unimplemented
lineageTransform _ _ (AppE (SubString _ _)  _) = $unimplemented
lineageTransform _ _ (AppE Sin              _) = $unimplemented
lineageTransform _ _ (AppE ASin             _) = $unimplemented
lineageTransform _ _ (AppE Cos              _) = $unimplemented
lineageTransform _ _ (AppE ACos             _) = $unimplemented
lineageTransform _ _ (AppE Tan              _) = $unimplemented
lineageTransform _ _ (AppE ATan             _) = $unimplemented
lineageTransform _ _ (AppE Sqrt             _) = $unimplemented
lineageTransform _ _ (AppE Exp              _) = $unimplemented
lineageTransform _ _ (AppE Log              _) = $unimplemented
lineageTransform _ _ (AppE AddDays          _) = $unimplemented
lineageTransform _ _ (AppE SubDays          _) = $unimplemented
lineageTransform _ _ (AppE DiffDays         _) = $unimplemented
lineageTransform _ _ (AppE DayDay           _) = $unimplemented
lineageTransform _ _ (AppE DayMonth         _) = $unimplemented
lineageTransform _ _ (AppE DayYear          _) = $unimplemented

-- We covered these functions already.  If they were to appear hear it would
-- mean they were passed an invalid number of arguments, which should never
-- happen.
lineageTransform _ _ (AppE Cons      _) = $impossible
lineageTransform _ _ (AppE ConcatMap _) = $impossible
lineageTransform _ _ (AppE Map       _) = $impossible
lineageTransform _ _ (AppE Append    _) = $impossible
lineageTransform _ _ (AppE Zip       _) = $impossible
-- let bindings are introduced by lineageTransform so it is not possible to
-- encounter one
lineageTransform _ _ (LetE _ _ _) = $impossible
-- Lambdas should only appear inside AppE arguments
lineageTransform _ _ (LamE _ _  ) = $impossible

--------------------------------------------------------------------------------
--             ACCESSING LINEAGE DATA AND PROVENANCE COMPONENTS               --
--------------------------------------------------------------------------------

-- | Extract data from a lineage-annotated row
lineageDataQ :: (QA a, QA k) => Q (Lineage a k) -> Q a
lineageDataQ (view -> (a, _)) = a

-- | Extract lineage from a lineage-annotated row
lineageProvQ :: (QA a, QA k) => Q (Lineage a k) -> Q (LineageAnnot k)
lineageProvQ (view -> (_, lin)) = lin

-- | Attach empty lineage to a value
emptyLineageQ :: (QA a, QA k) => Q a -> Q (Lineage a k)
emptyLineageQ (Q a) = Q (emptyLineageE mkReify a)

--------------------------------------------------------------------------------
--                      SMART HELPERS FOR CONSTRUCTING EXP                    --
--------------------------------------------------------------------------------

-- | Lineage constructor
lineageE :: Exp a -> Exp (LineageAnnotE k) -> Exp (LineageE a k)
lineageE row lin = TupleConstE (Tuple2E row lin)

-- | Attach empty lineage to a value
emptyLineageE :: DReify k -> Exp a -> Exp (LineageE a k)
emptyLineageE reifyK a =
    let reifyAnnot Proxy = TupleT (Tuple2T TextT (reifyK Proxy))
    in TupleConstE (Tuple2E a (ListE reifyAnnot (S.empty)))

-- | Lineage annotation constructor
lineageAnnotE :: DReify k -> Text -> Exp k -> Exp (LineageAnnotE k)
lineageAnnotE reifyK table_name key =
    singletonE (\Proxy -> TupleT $ Tuple2T TextT (reifyK Proxy))
               (TupleConstE (Tuple2E (TextE table_name) key))

-- | Append two lineage annotations
lineageAppendE :: Exp (LineageAnnotE k) -> Exp (LineageAnnotE k)
               -> Exp (LineageAnnotE k)
lineageAppendE a b = AppE Append (pairE a b)

-- | Construct a singleton list
singletonE :: DReify a -> Exp a -> Exp [a]
singletonE dreify = ListE dreify . S.singleton

-- | Extract data from a lineage-annotated row
lineageDataE :: Exp (LineageE a k) -> Exp a
lineageDataE = AppE (TupElem Tup2_1)

-- | Extract lineage from a lineage-annotated row
lineageProvE :: Exp (LineageE a k) -> Exp (LineageAnnotE k)
lineageProvE = AppE (TupElem Tup2_2)

-- | Construct a lambda that adds empty lineage to its argument:
--
--    (\a -> emptyLineageE a)
--
emptyLineageLamE :: forall a k. DReify a -> DReify k -> Integer
                 -> Exp (LineageE a k)
emptyLineageLamE reifyA reifyK x = emptyLineageE reifyK (VarE reifyA x)

-- | Add empty lineage to all elements in a list:
--
--    map (\a -> emptyLineageE a) e
--
emptyLineageListE :: DReify a -> DReify k -> Exp [a] -> Exp [LineageE a k]
emptyLineageListE reifyA reifyK e =
    AppE Map (TupleConstE (Tuple2E
              (LamE reifyA (emptyLineageLamE reifyA reifyK)) e))

--------------------------------------------------------------------------------
--                              SUBSTITUTION                                  --
--------------------------------------------------------------------------------

-- | Substitute variable x for variable v in an expression
subst :: Integer -> Integer -> Exp b -> Exp b
subst x v (VarE r e)      | v == e    = VarE r x
                          | otherwise = VarE r e
subst _ _  UnitE          = UnitE
subst _ _ (BoolE b)       = BoolE b
subst _ _ (CharE c)       = CharE c
subst _ _ (DoubleE d)     = DoubleE d
subst _ _ (IntegerE i)    = IntegerE i
subst _ _ (TextE t)       = TextE t
subst _ _ (DecimalE d)    = DecimalE d
subst _ _ (ScientificE s) = ScientificE s
subst _ _ (DayE d)        = DayE d
subst x v (ListE r l)     = ListE r (fmap (subst x v) l)
subst x v (AppE f e)      = AppE f (subst x v e)
subst x v (LamE r f)      = LamE r (\y -> subst x v (f y))
subst _ _ (TableE t k)    = TableE t k
subst x v (TupleConstE t) =
    let substTuple :: TupleConst a -> TupleConst a
        substTuple = $(mkSubstTuple 'x 'v 16)
    in TupleConstE (substTuple t)
subst x v (LetE b e1 e2)  | v == b    = LetE b (subst x v e1) e2
                          | otherwise = LetE b (subst x v e1) (subst x v e2)
