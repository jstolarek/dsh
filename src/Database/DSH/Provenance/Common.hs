{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-- | This module contains basic data types to represent where-provenance and
-- lineage
module Database.DSH.Provenance.Common (
   -- * Where-provenance data types
   WhereProvAnnot(..), WhereProv(..), ProvData, ProvAnnot,

   -- * Lineage data types
   Lineage, LineageE, LineageAnnot, LineageAnnotE, LineageTransform, QLT(..)

 ) where


import           Data.Decimal
import           Data.Default
import           Data.Proxy
import           Data.Scientific
import qualified Data.Set      as Set
import           Data.Text
import           Data.Time.Calendar               (Day)
import           Data.Type.Equality

import           Database.DSH.Common.Impossible
import           Database.DSH.Frontend.BasicType
import           Database.DSH.Frontend.Externals ()
import           Database.DSH.Frontend.Internals
import           Database.DSH.Frontend.TH
import           Database.DSH.Frontend.TupleTypes

--------------------------------------------------------------------------------
--                      WHERE-PROVENANCE DATA TYPES                           --
--------------------------------------------------------------------------------

-- | Data type that represents where-provenance as a value containing table
-- name, column name and row key.  Representation is abstract.  It cannot be
-- constructed by the programmer and projections are possible only with accessor
-- functions.
data WhereProvAnnot a = WhereProvAnnot
    { where_prov_table  :: Text
    , where_prov_column :: Text
    , where_prov_key    :: a
    }

-- | GADT that represents database values that can be annotated with provenance
-- annotation.  BasicType constraint ensures that we can only attach provenance
-- to values that can actually be stored in a data base cell.
data WhereProv a key where
    NoProv    :: BasicType a => a -> WhereProv a key
    WhereProv :: BasicType a => a -> WhereProvAnnot key -> WhereProv a key

-- | Extracts type of data stored in WhereProv
type family ProvData a where
    ProvData (WhereProv a _) = a

-- | Extracts type of annotation stored in WhereProv.  Note that WhereProv
-- implicitly represents a Maybe and we are explicit about that Maybe when
-- returning annotation type.
type family ProvAnnot a where
    ProvAnnot (WhereProv _ key) = Maybe (WhereProvAnnot key)

instance (Show key) => Show (WhereProvAnnot key) where
    show (WhereProvAnnot t c k) = "( table = "  ++ show t ++
                                  ", column = " ++ show c ++
                                  ", key = "    ++ show k ++ " )"

-- A Default instance is required to internally represent WhereProv data type
-- when no where-provenance is attached to a value.
instance (Default a) => Default (WhereProvAnnot a) where
    def = WhereProvAnnot (pack "") (pack "") (def :: a)

deriveQA   ''WhereProvAnnot
deriveView ''WhereProvAnnot

-- This instance is written by hand, rather than derived, to avoid erronous
-- BasicType constraint - we don't want to store WhereProvAnnot in a database
-- and so the row key can be anything.
instance TA (WhereProvAnnot a)

instance (Show a, Show b) => Show (WhereProv a b) where
    show (NoProv    d  ) = "( data = " ++ show d ++
                           ", prov = _|_ )"
    show (WhereProv d p) = "( data = " ++ show d ++
                           ", prov = " ++ show p ++ " )"

instance (BasicType a, QA a, QA key, Default key) => QA (WhereProv a key) where
  type Rep (WhereProv a key) = (Rep a, (Rep Bool, Rep (WhereProvAnnot key)))
  toExp (NoProv    d  ) = pairE (toExp d) (pairE (BoolE False)
                                           (toExp (def :: WhereProvAnnot key)))
  toExp (WhereProv d p) = pairE (toExp d) (pairE (BoolE True) (toExp p))
  frExp (TupleConstE (Tuple2E d (TupleConstE (Tuple2E (BoolE False) _)))) =
      NoProv (frExp d)
  frExp (TupleConstE (Tuple2E d (TupleConstE (Tuple2E (BoolE True ) p)))) =
      WhereProv (frExp d) (frExp p)
  frExp _                           = $impossible

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
    LineageTransform (a -> b)   t =  a -> b
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

-- | QLT instance for WhereProv allows composing where-provenance and lineage
instance (QA a, BasicType a, QA k, Default k) => QLT (WhereProv a k) where
    type LT (WhereProv a k) k1 = Lineage (WhereProv a k) k1
    ltEq _ k = case ltEq (Proxy :: Proxy (WhereProv a k)) k of
                 Refl -> Refl

--     ltEq :: forall k. (QA k) => Proxy a -> Proxy k
--         -> LineageTransform (Rep a) (Rep k) :~: Rep (LT a k)
--  type Rep (WhereProv a key) = (Rep a, (Rep Bool, Rep (WhereProvAnnot key)))

{-
 ltEq (Proxy (WhereProv a k)) (Proxy k)

    • Couldn't match type ‘(Bool, (Text, Text, LineageTransform (Rep k) (Rep k1)))’
                     with ‘[(Text, Rep k1)]’




LineageTransform (Rep (WhereProv a k)) (Rep k) :~: Rep (LT (WhereProv a k) k)





      Expected type:  LineageTransform (Rep (WhereProv a k)) (Rep k1) :~: Rep (LT (WhereProv a k) k1)
        Actual type: (LineageTransform (Rep a) (Rep k1), (Bool, (Text, Text, LineageTransform (Rep k) (Rep k1))))
                 :~: (LineageTransform (Rep a) (Rep k1), (Bool, (Text, Text, LineageTransform (Rep k) (Rep k1))))

LHS

LineageTransform (Rep (WhereProv a k)) (Rep k1)

LineageTransform (Rep a, (Rep Bool, Rep (WhereProvAnnot k))) (Rep k1)

(LineageTransform (Rep a) (Rep k1), LineageTransform (Rep Bool, Rep (WhereProvAnnot k)) (Rep k1))

(LineageTransform (Rep a) (Rep k1), (LineageTransform (Rep Bool) (Rep k1), LineageTransform  (Rep (WhereProvAnnot k)) (Rep k1)))

(LineageTransform (Rep a) (Rep k1), (Bool, LineageTransform (Rep (WhereProvAnnot k)) (Rep k1)))

(LineageTransform (Rep a) (Rep k1), (Bool, LineageTransform (Text, Text, Rep k) (Rep k1)))

(LineageTransform (Rep a) (Rep k1), (Bool, (Text, Text, LineageTransform (Rep k) (Rep k1))))


RHS

Rep (Lineage (WhereProv a k) k1)

((Rep a, (Rep Bool, Rep (WhereProvAnnot k))), Rep [LineageAnnotEntry k1])

-}
