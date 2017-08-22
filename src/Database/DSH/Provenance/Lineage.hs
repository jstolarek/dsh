{-# LANGUAGE GADTs                #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Database.DSH.Provenance.Lineage
    ( -- * Lineage transformation and data type
      lineage, Lineage

      -- * Accessing data and provenance components of lineage-annotated value
    , lineageDataQ, lineageProvQ, emptyLineageQ
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
    Lineage  :: a -> LineageAnnot k -> Lineage a k

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

-- | Perform lineage transformation on a query
lineage :: forall a k. (Reify (Rep a), Reify (Rep k), Typeable (Rep k))
        => Q [a] -> Q [Lineage a k]
lineage (Q a) = Q (runLineage (lineageTransform (Proxy :: Proxy (Rep k)) a))

type family LineageTransform a k where
    LineageTransform ()         k =  LineageE () k
    LineageTransform Bool       k =  LineageE Bool k
    LineageTransform Char       k =  LineageE Char k
    LineageTransform Integer    k =  LineageE Integer k
    LineageTransform Double     k =  LineageE Double k
    LineageTransform Text       k =  LineageE Text k
    LineageTransform Decimal    k =  LineageE Decimal k
    LineageTransform Scientific k =  LineageE Scientific k
    LineageTransform Day        k =  LineageE Day k
    LineageTransform [a]        k = [LineageE a k]
    LineageTransform (a,b)      k = (LineageE a k, LineageE b k)
    LineageTransform (a,b,c)    k = (LineageE a k, LineageE b k, LineageE c k)
    -- JSTOLAREK: more tuple types, up to 16

lineageTransform :: forall a k. ( Reify a, Reify k, Typeable k
                                , Reify (LineageTransform a k))
                 => Proxy k -> Exp a -> Compile (Exp (LineageTransform a k))
lineageTransform proxy t@(TableE (TableDB name _ _) keyProj) = do
  let -- We have to perform runtime type equality to check that type of lineage
      -- key specified in a call to `lineage` matches the type returned by
      -- `keyProj` function stored in `TableE` constructor.
      keyEquality :: forall k1 k2. (Typeable k1, Typeable k2)
                  => Proxy k1 -> (Integer -> Exp k2) -> Maybe (k1 :~: k2)
      keyEquality _ _ = eqT
  case keyEquality proxy keyProj of
    Just Refl -> do
      let lam :: Reify b => Integer -> Exp (b, LineageAnnotE k)
          lam a = lineageE (VarE Proxy a)
                     (lineageAnnotE (pack name) (keyProj a :: Exp k))
      return (AppE Proxy Map (TupleConstE (Tuple2E (LamE lam) t)))
    Nothing -> $impossible

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
      lamAppend al z = lineageE (lineageDataE (VarE proxy' z))
                        ((lineageProvE (VarE proxy'' al)) `lineageAppendE`
                         (lineageProvE (VarE proxy'  z)))

      -- comprehension that appends lineages of currently traversed collection
      -- and result of nested part of comprehension
      compLineageApp al = AppE (proxyLineageApp proxy) Map (TupleConstE
             (Tuple2E (LamE (lamAppend al)) bodyExp))

      -- comprehension over singleton list containing data originally assigned
      -- to comprehension binder
      compSingOrg al = AppE (proxySingOrg proxy) ConcatMap (TupleConstE
             (Tuple2E (LamE (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE (lineageDataE
                                   (VarE (proxyLineageElem proxy'') al)))))
  return (AppE Proxy
               ConcatMap (TupleConstE (Tuple2E (LamE compSingOrg) tbl')))

lineageTransform k (AppE proxy ConcatMap
                    (TupleConstE (Tuple2E (LamE lam) tbl))) = do
  -- translate the comprehension generator
  tbl' <- lineageTransform k tbl
  -- saturate the lambda and translate the resulting expression
  boundVar <- freshVar
  bodyExp  <- lineageTransform k (lam boundVar)

  let -- Specialized proxy transformers
      proxyRes :: Proxy (x -> [y], [x]) -> Proxy [y]
      proxyRes Proxy = Proxy

      proxyLineageApp :: Proxy (x -> [y], [x])
                      -> Proxy (LineageE y k -> LineageE y k, [LineageE y k])
      proxyLineageApp Proxy = Proxy

      proxySingOrg :: Proxy (x -> [y], [x]) -> Proxy (x -> [LineageE y k], [x])
      proxySingOrg Proxy = Proxy

      -- proxies needed to guide variable types
      proxy'  = proxyLineage (proxyElem (proxyRes proxy))
      proxy'' = proxyLineage (proxySnd proxy)

      -- lambda that appends lineages
      lamAppend al z = lineageE (lineageDataE (VarE proxy' z))
                        ((lineageProvE (VarE proxy'' al)) `lineageAppendE`
                         (lineageProvE (VarE proxy'  z)))

      -- comprehension that appends lineages of currently traversed collection
      -- and result of nested part of comprehension
      compLineageApp al = AppE (proxyLineageApp proxy) Map (TupleConstE
             (Tuple2E (LamE (lamAppend al)) bodyExp))

      -- comprehension over singleton list containing data originally assigned
      -- to comprehension binder
{-
      compSingOrg al = LetE boundVar (lineageDataE (VarE (proxyLineageElem proxy'') al))
                       (compLineageApp al)
-}

      compSingOrg al = AppE (proxySingOrg proxy) ConcatMap (TupleConstE
             (Tuple2E (LamE (\a -> subst a boundVar (compLineageApp al)))
                      (singletonE (lineageDataE
                                   (VarE (proxyLineageElem proxy'') al)))))
  return (AppE Proxy
               ConcatMap (TupleConstE (Tuple2E (LamE compSingOrg) tbl')))

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
lineageE :: (Reify a, Reify k)
         => Exp a -> Exp (LineageAnnotE k) -> Exp (LineageE a k)
lineageE row lin = TupleConstE (Tuple2E row lin)

-- | Attach empty lineage to a value
emptyLineageE :: (Reify a, Reify k) => Exp a -> Exp (LineageE a k)
emptyLineageE a = TupleConstE (Tuple2E a (ListE (S.empty)))

-- | Lineage annotation constructor
lineageAnnotE :: Reify k => Text -> Exp k -> Exp (LineageAnnotE k)
lineageAnnotE table_name key =
    singletonE (TupleConstE (Tuple2E (TextE table_name) key))

-- | Append two lineage annotations
lineageAppendE :: Reify k => Exp (LineageAnnotE k) -> Exp (LineageAnnotE k)
               -> Exp (LineageAnnotE k)
lineageAppendE a b = AppE Proxy Append (pairE a b)

-- | Construct a singleton list
singletonE :: Reify a => Exp a -> Exp [a]
singletonE = ListE . S.singleton

-- | Extract data from a lineage-annotated row
lineageDataE :: (Reify a, Reify k) => Exp (LineageE a k) -> Exp a
lineageDataE = AppE Proxy (TupElem Tup2_1)

-- | Extract lineage from a lineage-annotated row
lineageProvE :: (Reify a, Reify k)
             => Exp (LineageE a k) -> Exp (LineageAnnotE k)
lineageProvE = AppE Proxy (TupElem Tup2_2)

-- | Construct a lambda that adds empty lineage to its argument:
--
--    (\a -> emptyLineageE a)
--
emptyLineageLamE :: forall a k. (Reify a, Reify k)
                 => Integer -> Exp (LineageE a k)
emptyLineageLamE x = emptyLineageE (VarE (Proxy :: Proxy a) x)

-- | Add empty lineage to all elements in a list:
--
--    map (\a -> emptyLineageE a) e
--
emptyLineageListE :: (Reify a, Reify k) => Exp [a] -> Exp [LineageE a k]
emptyLineageListE e =
    AppE Proxy Map (TupleConstE (Tuple2E (LamE emptyLineageLamE) e))


--------------------------------------------------------------------------------
--                           PROXY TRANSFORMERS                               --
--------------------------------------------------------------------------------

-- These functions convert between various proxy types.  They are used to guide
-- type inference by hand when constructing expressions.  These are
-- general-purpose proxy transformers used by several functions.  Specialized
-- transformers used by only one function are defined within functions.

-- | Return type of list element
proxyElem :: Proxy [a] -> Proxy a
proxyElem Proxy = Proxy

-- | Return type of row augmented with lineage information
proxyLineage :: Proxy a -> Proxy (LineageE a k)
proxyLineage Proxy = Proxy

-- | Return type of second component of a tuple
proxySnd :: Proxy (a, b) -> Proxy b
proxySnd Proxy = Proxy

-- | Specialized proxy
proxyLineageElem :: Proxy (LineageE [b] k) -> Proxy (LineageE b k)
proxyLineageElem Proxy = Proxy

--------------------------------------------------------------------------------
--                              SUBSTITUTION                                  --
--------------------------------------------------------------------------------

-- | Substitute variable x for variable v in an expression
subst :: Integer -> Integer -> Exp b -> Exp b
subst x v (VarE _ e)      | v == e    = VarE Proxy x
                          | otherwise = VarE Proxy e
subst _ _  UnitE          = UnitE
subst _ _ (BoolE b)       = BoolE b
subst _ _ (CharE c)       = CharE c
subst _ _ (DoubleE d)     = DoubleE d
subst _ _ (IntegerE i)    = IntegerE i
subst _ _ (TextE t)       = TextE t
subst _ _ (DecimalE d)    = DecimalE d
subst _ _ (ScientificE s) = ScientificE s
subst _ _ (DayE d)        = DayE d
subst x v (ListE l)       = ListE (fmap (subst x v) l)
subst x v (AppE p f e)    = AppE p f (subst x v e)
subst x v (LamE f)        = LamE (\y -> subst x v (f y))
subst _ _ (TableE t k)    = TableE t k
subst x v (TupleConstE t) =
    let substTuple :: TupleConst a -> TupleConst a
        substTuple = $(mkSubstTuple 'x 'v 16)
    in TupleConstE (substTuple t)
subst x v (LetE b e1 e2)  | v == b    = LetE b (subst x v e1) e2
                          | otherwise = LetE b (subst x v e1) (subst x v e2)
