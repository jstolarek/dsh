{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Database.DSH.Frontend.Internals (
   module Database.DSH.Frontend.BasicType
 , module Database.DSH.Frontend.Internals
 ) where

import qualified Data.Sequence as S
import           Data.Decimal
import           Data.Scientific
import           Data.List.NonEmpty               (NonEmpty)
import           Data.Proxy
import           Data.Text                        (Text)
import           Data.Time.Calendar               (Day)
import           Data.Typeable
import           Text.PrettyPrint.ANSI.Leijen

import           Database.DSH.Common.Impossible
import           Database.DSH.Frontend.BasicType
import           Database.DSH.Frontend.TupleTypes

-- Splice in the type for tuple element accessors
$(mkTupElemType 16)

-- Generate the data types 'TupleConst' and 'TupleType' for tuple term
-- and type construction.
$(mkTupleAstComponents 16)

--------------------------------------------------------------------------------
-- Classes

class Reify a where
    reify :: a -> Type a

class (Reify (Rep a)) => QA a where
    type Rep a
    toExp :: a -> Exp (Rep a)
    frExp :: Exp (Rep a) -> a

class (QA a,QA r) => Elim a r where
    type Eliminator a r
    elim :: Q a -> Eliminator a r

class TA a where

class View a where
    type ToView a
    view :: a -> ToView a

newtype Q a = Q (Exp (Rep a))

data DReify a = MkReify (a -> Type a)

--------------------------------------------------------------------------------
-- Typed frontend ASTs

data Fun a b where
    Not              :: Fun Bool Bool
    IntegerToDouble  :: Fun Integer Double
    IntegerToDecimal :: Fun Integer Decimal
    And              :: Fun [Bool] Bool
    Or               :: Fun [Bool] Bool
    Concat           :: Fun [[a]] [a]
    Null             :: Fun [a] Bool
    Length           :: Fun [a] Integer
    Only             :: Fun [a] a
    Guard            :: Fun Bool [()]
    Reverse          :: Fun [a] [a]
    Number           :: Fun [a] [(a, Integer)]
    Fst              :: Fun (a,b) a
    Snd              :: Fun (a,b) b
    Sum              :: Fun [a] a
    Avg              :: Fun [a] a
    Maximum          :: Fun [a] a
    Minimum          :: Fun [a] a
    Nub              :: Fun [a] [a]
    Append           :: Fun ([a], [a]) [a]
    Add              :: Fun (a,a) a
    Mul              :: Fun (a,a) a
    Sub              :: Fun (a,a) a
    Div              :: Fun (a,a) a
    Mod              :: Fun (Integer,Integer) Integer
    Lt               :: Fun (a,a) Bool
    Lte              :: Fun (a,a) Bool
    Equ              :: Fun (a,a) Bool
    NEq              :: Fun (a,a) Bool
    Gte              :: Fun (a,a) Bool
    Gt               :: Fun (a,a) Bool
    Conj             :: Fun (Bool,Bool) Bool
    Disj             :: Fun (Bool,Bool) Bool
    Cons             :: Fun (a,[a]) [a]
    Zip              :: Fun ([a],[b]) [(a,b)]
    Map              :: Fun (a -> b,[a]) [b]
    ConcatMap        :: Reify b => Fun (a -> [b],[a]) [b]
    Filter           :: Fun (a -> Bool,[a]) [a]
    GroupWithKey     :: Fun (a -> b,[a]) [(b, [a])]
    SortWith         :: Fun (a -> b,[a]) [a]
    Cond             :: Fun (Bool,a,a) a
    Like             :: Fun (Text,Text) Bool
    SubString        :: Integer -> Integer -> Fun Text Text
    Sin              :: Fun Double Double
    Cos              :: Fun Double Double
    Tan              :: Fun Double Double
    Sqrt             :: Fun Double Double
    Exp              :: Fun Double Double
    Log              :: Fun Double Double
    ASin             :: Fun Double Double
    ACos             :: Fun Double Double
    ATan             :: Fun Double Double
    AddDays          :: Fun (Integer, Day) Day
    SubDays          :: Fun (Integer, Day) Day
    DiffDays         :: Fun (Day, Day) Integer
    DayDay           :: Fun Day Integer
    DayMonth         :: Fun Day Integer
    DayYear          :: Fun Day Integer
    TupElem          :: TupElem a b -> Fun a b

data Exp a where
    UnitE       :: Exp ()
    BoolE       :: !Bool    -> Exp Bool
    CharE       :: !Char    -> Exp Char
    IntegerE    :: !Integer -> Exp Integer
    DoubleE     :: !Double  -> Exp Double
    TextE       :: !Text    -> Exp Text
    DecimalE    :: !Decimal -> Exp Decimal
    ScientificE :: !Scientific -> Exp Scientific
    DayE        :: !Day     -> Exp Day
    ListE       :: DReify a -> !(S.Seq (Exp a)) -> Exp [a]
    AppE        :: Proxy a -> Fun a b -> Exp a -> Exp b
    LamE        :: (Integer -> Exp b) -> Exp (a -> b)
    VarE        :: DReify a -> Integer -> Exp a
    TableE      :: (Reify a, Typeable k)
                => Table -> (Integer -> Exp k) -> Exp [a]
    TupleConstE :: !(TupleConst a) -> Exp a
    LetE        :: Integer -> Exp a -> Exp b -> Exp b

data Type a where
    UnitT       :: Type ()
    BoolT       :: Type Bool
    CharT       :: Type Char
    IntegerT    :: Type Integer
    DoubleT     :: Type Double
    TextT       :: Type Text
    DecimalT    :: Type Decimal
    ScientificT :: Type Scientific
    DayT        :: Type Day
    ListT       :: Type a -> Type [a]
    ArrowT      :: Type a -> Type b -> Type (a -> b)
    TupleT      :: TupleType a -> Type a

instance Pretty (Type a) where
    pretty UnitT          = text "()"
    pretty BoolT          = text "Bool"
    pretty CharT          = text "Char"
    pretty IntegerT       = text "Integer"
    pretty DoubleT        = text "Double"
    pretty TextT          = text "Text"
    pretty DecimalT       = text "Decimal"
    pretty ScientificT    = text "Scientific"
    pretty DayT           = text "Day"
    pretty (ListT t)      = brackets $ pretty t
    pretty (ArrowT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2
    pretty (TupleT t)     = pretty t

-- FIXME generate with TH
instance Pretty (TupleType a) where
    pretty (Tuple2T t1 t2) = tupled [pretty t1, pretty t2]
    pretty _               = $unimplemented

pairE :: Exp a -> Exp b -> Exp (a, b)
pairE a b = TupleConstE (Tuple2E a b)

tripleE :: Exp a -> Exp b -> Exp c -> Exp (a, b, c)
tripleE a b c = TupleConstE (Tuple3E a b c)

--------------------------------------------------------------------------------
-- Definition of database-resident tables

-- | A combination of column names that form a candidate key
newtype Key = Key { unKey :: NonEmpty String } deriving (Eq, Ord, Show)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

-- | Do we track where-provenance, and if so then for which fields?
data Provenance = NoProvenance
                | WhereProvenance (NonEmpty String)
                deriving (Eq, Ord, Show)

type ColName = String

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints
    { keysHint       :: NonEmpty Key
    , nonEmptyHint   :: Emptiness
    , provenanceHint :: Provenance
    } deriving (Eq, Ord, Show)

data Table = TableDB String (NonEmpty ColName) TableHints

clearTableProvenance :: Table -> Table
clearTableProvenance (TableDB n cs (TableHints k e _)) =
    TableDB n cs (TableHints k e NoProvenance)

-- Reify instances

instance Reify () where
    reify _ = UnitT

instance Reify Bool where
    reify _ = BoolT

instance Reify Char where
    reify _ = CharT

instance Reify Integer where
    reify _ = IntegerT

instance Reify Double where
    reify _ = DoubleT

instance Reify Decimal where
    reify _ = DecimalT

instance Reify Scientific where
    reify _ = ScientificT

instance Reify Text where
    reify _ = TextT

instance Reify Day where
  reify _ = DayT

instance (Reify a) => Reify [a] where
    reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
    reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

-- Utility functions

unQ :: Q a -> Exp (Rep a)
unQ (Q e) = e

toLam :: (QA a, QA b) => (Q a -> Q b) -> Integer -> Exp (Rep b)
toLam f = unQ . f . Q . (VarE mkReify)

mkReify :: Reify a => DReify a
mkReify = MkReify reify

-- * Generate Reify instances for tuple types
mkReifyInstances 16
