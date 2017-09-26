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
      lineage, Lineage

      -- * Accessing data and provenance components of lineage-annotated value
--    , lineageDataQ, lineageProvQ, emptyLineageQ
    ) where

import           Data.Decimal
import           Data.Proxy
import           Data.Text
import           Data.Time.Calendar               (Day)
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
    LineageTransform ()         k =  ()
    LineageTransform Bool       k =  Bool
    LineageTransform Char       k =  Char
    LineageTransform Integer    k =  Integer
    LineageTransform Double     k =  Double
    LineageTransform Text       k =  Text
    LineageTransform Decimal    k =  Decimal
    LineageTransform Scientific k =  Scientific
    LineageTransform Day        k =  Day
    LineageTransform (a -> b)   k =  a -> b
    LineageTransform [a]        k = [LineageE (LineageTransform a k) k]
    LineageTransform (a,b)      k = (LineageTransform a k, LineageTransform b k)
    -- JSTOLAREK: these definitions inconsistent with pair definition
    LineageTransform (a,b,c)    k = (LineageE a k, LineageE b k, LineageE c k)
    LineageTransform (a,b,c,d)  k = ( LineageE a k, LineageE b k, LineageE c k
                                    , LineageE d k)
    -- JSTOLAREK: more tuple types, up to 16

class (QA a) => QLTable a where
    type family LT a k
    ltEq :: forall k. (QA k) => Proxy a -> Proxy k
         -> LineageTransform (Rep a) (Rep k) :~: Rep (LT a k)

instance QLTable () where
    type LT () k = () --Lineage () k
    ltEq _ _ = Refl

instance QLTable Bool where
    type LT Bool k = Bool -- Lineage Bool k
    ltEq _ _ = Refl

instance QLTable Char where
    type LT Char k = Char -- Lineage Char k
    ltEq _ _ = Refl

instance QLTable Integer where
    type LT Integer k = Integer -- Lineage Integer k
    ltEq _ _ = Refl

instance QLTable Double where
    type LT Double k = Double -- Lineage Double k
    ltEq _ _ = Refl

instance QLTable Text where
    type LT Text k = Text -- Lineage Text k
    ltEq _ _ = Refl

instance QLTable Decimal where
    type LT Decimal k = Decimal -- Lineage Decimal k
    ltEq _ _ = Refl

instance QLTable Scientific where
    type LT Scientific k = Scientific -- Lineage Scientific k
    ltEq _ _ = Refl

instance QLTable Day where
    type LT Day k = Day -- Lineage Day k
    ltEq _ _ = Refl

instance QLTable a => QLTable [a] where
    type LT [a] k = [Lineage (LT a k) k]
    ltEq _ k = case ltEq (Proxy :: Proxy a) k of
                 Refl -> Refl

instance (QLTable a, QLTable b) => QLTable (a, b) where
    type LT (a, b) k = (LT a k, LT b k)
    ltEq _ k = case (ltEq (Proxy :: Proxy a) k, ltEq (Proxy :: Proxy b) k) of
                 (Refl, Refl) -> Refl

instance (QLTable a, QLTable b, QLTable c)
    => QLTable (a, b, c) where
    type LT (a, b, c) k = (Lineage a k, Lineage b k, Lineage c k)
    ltEq _ k =
        let ltEqA = ltEq (Proxy :: Proxy a) k
            ltEqB = ltEq (Proxy :: Proxy b) k
            ltEqC = ltEq (Proxy :: Proxy c) k
        in case (ltEqA, ltEqB, ltEqC) of
             (Refl, Refl, Refl) -> Refl

instance (QLTable a, QLTable b, QLTable c, QLTable d)
    => QLTable (a, b, c, d) where
    type LT (a, b, c, d) k = (Lineage a k, Lineage b k, Lineage c k, Lineage d k)
    ltEq _ k =
        let ltEqA = ltEq (Proxy :: Proxy a) k
            ltEqB = ltEq (Proxy :: Proxy b) k
            ltEqC = ltEq (Proxy :: Proxy c) k
            ltEqD = ltEq (Proxy :: Proxy d) k
        in case (ltEqA, ltEqB, ltEqC, ltEqD) of
             (Refl, Refl, Refl, Refl) -> Refl

-- | Perform lineage transformation on a query
lineage :: forall a k.
           ( Reify (Rep a), QA k, Typeable (Rep k), QLTable a
           , Reify (LineageTransform (Rep a) (Rep k)) )
        => Proxy k -> Q a -> Q (LT a k)
lineage pk (Q a) =
   let pa  = Proxy :: Proxy a
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
typeLT (ArrowT fun arg) _ = (ArrowT fun arg)
typeLT (ListT lt) kt = ListT (TupleT $ Tuple2T (typeLT lt kt)
                                            (ListT (TupleT $ Tuple2T TextT kt)))
typeLT (TupleT (Tuple2T a b)) kt = TupleT (Tuple2T (typeLT a kt) (typeLT b kt))
-- JSTOLAREK: these definitions inconsistent with pair definition
typeLT (TupleT (Tuple3T a b c)) kt = TupleT (Tuple3T
     (TupleT $ Tuple2T a (ListT (TupleT $ Tuple2T TextT kt)))
     (TupleT $ Tuple2T b (ListT (TupleT $ Tuple2T TextT kt)))
     (TupleT $ Tuple2T c (ListT (TupleT $ Tuple2T TextT kt))))
typeLT (TupleT (Tuple4T a b c d)) kt = TupleT (Tuple4T
     (TupleT $ Tuple2T a (ListT (TupleT $ Tuple2T TextT kt)))
     (TupleT $ Tuple2T b (ListT (TupleT $ Tuple2T TextT kt)))
     (TupleT $ Tuple2T c (ListT (TupleT $ Tuple2T TextT kt)))
     (TupleT $ Tuple2T d (ListT (TupleT $ Tuple2T TextT kt))))
-- JSTOLAREK: add tuple support up to 16, use TH
typeLT _ _ = $unimplemented


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
    Nothing -> $impossible

lineageTransform reifyA reifyK (AppE ConcatMap
                   (TupleConstE (Tuple2E (LamE reifyC lam) tbl))) = do

  -- translate the comprehension generator
  -- tbl' :: Exp [LineageE (LineageTransform a4 k) k]
  let reifyCs Proxy = ListT (reifyC Proxy)
  tbl' <- lineageTransform reifyCs reifyK tbl
  -- saturate the lambda and translate the resulting expression
  boundVar <- freshVar
  --  bodyExp :: Exp [LineageE (LineageTransform b1 k) k]
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
{-
      compSingOrg al = LetE boundVar (lineageDataE (VarE (proxyLineageElem proxy'') al))
                       (compLineageApp al)
-}

      compSingOrg al = AppE ConcatMap (TupleConstE
             (Tuple2E (LamE reifyTy'
                            (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE reifyTy' (lineageDataE
                                   (VarE reifyTy al)))))
  return (AppE ConcatMap (TupleConstE (Tuple2E
                                       (LamE reifyTy'' compSingOrg) tbl')))

{-
lineageTransform k (AppE proxy Map
                    (TupleConstE (Tuple2E (LamE lam) tbl))) = do
  -- translate the comprehension generator
  tbl' <- lineageTransform k tbl
  -- saturate the lambda and translate the resulting expression
  boundVar <- freshVar
  bodyExp  <- lineageTransform k (singletonE (lam boundVar))

  let -- Specialized proxy transformers
      proxyRes :: Proxy (x -> y, [x]) -> Proxy y
      proxyRes Proxy = Proxy

      proxyLineageApp :: Proxy (x -> y, [x])
                      -> Proxy (LineageE y k -> LineageE y k, [LineageE y k])
      proxyLineageApp Proxy = Proxy

      proxySingOrg :: Proxy (x -> y, [x]) -> Proxy (x -> [LineageE y k], [x])
      proxySingOrg Proxy = Proxy

      -- proxies needed to guide variable types
      proxy'  = proxyLineage (proxyRes proxy)
      proxy'' = proxyLineage (proxySnd proxy)

      -- lambda that appends lineages
      lamAppend al z = lineageE (lineageDataE (VarE mkReify z))
                        ((lineageProvE (VarE mkReify al)) `lineageAppendE`
                         (lineageProvE (VarE mkReify  z)))

      -- comprehension that appends lineages of currently traversed collection
      -- and result of nested part of comprehension
      compLineageApp al = AppE (proxyLineageApp proxy) Map (TupleConstE
             (Tuple2E (LamE (lamAppend al)) bodyExp))

      -- comprehension over singleton list containing data originally assigned
      -- to comprehension binder
      compSingOrg al = AppE (proxySingOrg proxy) ConcatMap (TupleConstE
             (Tuple2E (LamE (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE (lineageDataE
                                   (VarE mkReify al)))))
  return (AppE Proxy
               ConcatMap (TupleConstE (Tuple2E (LamE compSingOrg) tbl')))

lineageTransform _ _ = $unimplemented

lineageTransform _   (VarE _ v)       = return (VarE Proxy v)
{- JSTOLAREK: speculative
lineageTransform k e@(ListE xs)       = do
  xs' <- mapM (lineageTransform k) xs
  return (emptyLineageListE e)
-}
lineageTransform _ e@(ListE _)        = return (emptyLineageListE e)
{- JSTOLAREK: speculative
lineageTransform k e@(AppE _ Guard b) = do
  b' <- lineageTransform k b
  return (lineageE (AppE Proxy Guard (lineageDataE b')) (lineageProvE b'))
-}
lineageTransform _ e@(AppE _ Guard _) = return (emptyLineageListE e)
lineageTransform _ e@(AppE _ Cons (TupleConstE (Tuple2E _ _))) =
  return (emptyLineageListE e)

-- constants
lineageTransform _    UnitE          = return (emptyLineageE UnitE)
lineageTransform _ e@(BoolE       _) = return (emptyLineageE e)
lineageTransform _ e@(CharE       _) = return (emptyLineageE e)
lineageTransform _ e@(IntegerE    _) = return (emptyLineageE e)
lineageTransform _ e@(DoubleE     _) = return (emptyLineageE e)
lineageTransform _ e@(TextE       _) = return (emptyLineageE e)
lineageTransform _ e@(DayE        _) = return (emptyLineageE e)
lineageTransform _ e@(ScientificE _) = return (emptyLineageE e)
lineageTransform _ e@(DecimalE    _) = return (emptyLineageE e)

-- L(xs ++ ys) = L(xs) ++ L(ys)
lineageTransform k (AppE _ Append (TupleConstE (Tuple2E xs ys))) = do
  xs' <- lineageTransform k xs
  ys' <- lineageTransform k ys
  return (AppE Proxy Append (TupleConstE (Tuple2E xs' ys')))

-- L(reverse xs) = reverse (L(xs))
lineageTransform k (AppE _ Reverse xs) = do
  xs' <- lineageTransform k xs
  return (AppE Proxy Reverse xs')

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
lineageTransform _ (AppE _ Filter           _) = $unimplemented

-- concat has type [[a]] -> [a].  According to our TF declaration if input is
-- [[a]] the return type is [L [a]], but we want [L a].
lineageTransform _ (AppE _ Concat           _) = $unimplemented

lineageTransform _ (AppE _ Sum              _) = $unimplemented
lineageTransform _ (AppE _ Avg              _) = $unimplemented
lineageTransform _ (AppE _ Maximum          _) = $unimplemented
lineageTransform _ (AppE _ Minimum          _) = $unimplemented
lineageTransform _ (AppE _ Nub              _) = $unimplemented
lineageTransform _ (AppE _ Zip              _) = $unimplemented
lineageTransform _ (AppE _ GroupWithKey     _) = $unimplemented
lineageTransform _ (AppE _ SortWith         _) = $unimplemented
lineageTransform _ (AppE _ Cond             _) = $unimplemented
lineageTransform _ (AppE _ Fst              _) = $unimplemented
lineageTransform _ (AppE _ Snd              _) = $unimplemented
lineageTransform _ (AppE _ (TupElem _)      _) = $unimplemented
lineageTransform _ (AppE _ Only             _) = $unimplemented
lineageTransform _ (AppE _ Length           _) = $unimplemented
lineageTransform _ (AppE _ Null             _) = $unimplemented
lineageTransform _ (AppE _ Number           _) = $unimplemented
lineageTransform _ (AppE _ Add              _) = $unimplemented
lineageTransform _ (AppE _ Mul              _) = $unimplemented
lineageTransform _ (AppE _ Sub              _) = $unimplemented
lineageTransform _ (AppE _ Div              _) = $unimplemented
lineageTransform _ (AppE _ Mod              _) = $unimplemented
lineageTransform _ (AppE _ Not              _) = $unimplemented
lineageTransform _ (AppE _ And              _) = $unimplemented
lineageTransform _ (AppE _ Or               _) = $unimplemented
lineageTransform _ (AppE _ IntegerToDouble  _) = $unimplemented
lineageTransform _ (AppE _ IntegerToDecimal _) = $unimplemented
lineageTransform _ (AppE _ Lt               _) = $unimplemented
lineageTransform _ (AppE _ Lte              _) = $unimplemented
lineageTransform _ (AppE _ Gt               _) = $unimplemented
lineageTransform _ (AppE _ Gte              _) = $unimplemented
lineageTransform _ (AppE _ Equ              _) = $unimplemented
lineageTransform _ (AppE _ NEq              _) = $unimplemented
lineageTransform _ (AppE _ Conj             _) = $unimplemented
lineageTransform _ (AppE _ Disj             _) = $unimplemented
lineageTransform _ (AppE _ Like             _) = $unimplemented
lineageTransform _ (AppE _ (SubString _ _)  _) = $unimplemented
lineageTransform _ (AppE _ Sin              _) = $unimplemented
lineageTransform _ (AppE _ ASin             _) = $unimplemented
lineageTransform _ (AppE _ Cos              _) = $unimplemented
lineageTransform _ (AppE _ ACos             _) = $unimplemented
lineageTransform _ (AppE _ Tan              _) = $unimplemented
lineageTransform _ (AppE _ ATan             _) = $unimplemented
lineageTransform _ (AppE _ Sqrt             _) = $unimplemented
lineageTransform _ (AppE _ Exp              _) = $unimplemented
lineageTransform _ (AppE _ Log              _) = $unimplemented
lineageTransform _ (AppE _ AddDays          _) = $unimplemented
lineageTransform _ (AppE _ SubDays          _) = $unimplemented
lineageTransform _ (AppE _ DiffDays         _) = $unimplemented
lineageTransform _ (AppE _ DayDay           _) = $unimplemented
lineageTransform _ (AppE _ DayMonth         _) = $unimplemented
lineageTransform _ (AppE _ DayYear          _) = $unimplemented

-- We covered these functions already.  If they were to appear hear it would
-- mean they were passed an invalid number of arguments, which should never
-- happen.
lineageTransform _ (AppE _ Cons      _) = $impossible
lineageTransform _ (AppE _ ConcatMap _) = $impossible
lineageTransform _ (AppE _ Map       _) = $impossible
lineageTransform _ (AppE _ Append    _) = $impossible
lineageTransform _ (TupleConstE      _) = $impossible
-- let bindings are introduced by lineageTransform so it is not possible to
-- encounter one
lineageTransform _ (LetE _ _ _) = $impossible
-- JSTOLAREK: think about lambdas
lineageTransform _ (LamE _    ) = $impossible
-}

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
emptyLineageQ (Q a) = Q (emptyLineageE a)

--------------------------------------------------------------------------------
--                      SMART HELPERS FOR CONSTRUCTING EXP                    --
--------------------------------------------------------------------------------

-- | Lineage constructor
lineageE :: Exp a -> Exp (LineageAnnotE k) -> Exp (LineageE a k)
lineageE row lin = TupleConstE (Tuple2E row lin)

-- | Attach empty lineage to a value
emptyLineageE :: Reify k => Exp a -> Exp (LineageE a k)
emptyLineageE a = TupleConstE (Tuple2E a (ListE mkReify (S.empty)))

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
emptyLineageLamE :: forall a k. (Reify a, Reify k)
                 => Integer -> Exp (LineageE a k)
emptyLineageLamE x = emptyLineageE (VarE mkReify x)

-- | Add empty lineage to all elements in a list:
--
--    map (\a -> emptyLineageE a) e
--
emptyLineageListE :: (Reify a, Reify k) => Exp [a] -> Exp [LineageE a k]
emptyLineageListE e =
    AppE Map (TupleConstE (Tuple2E (LamE mkReify emptyLineageLamE) e))


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
