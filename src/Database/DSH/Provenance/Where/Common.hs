{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module contains data types to represent where-provenance
module Database.DSH.Provenance.Where.Common (

   WhereProvAnnot(..), WhereProv(..), ProvData, ProvAnnot

 ) where

import           Data.Text

import           Database.DSH.Frontend.BasicType

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
