{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | Where-provenance representation and manipulation
module Database.DSH.Provenance.Where (

   WhereProvAnnot, WhereProv, ProvData, ProvAnnot,
   where_prov_tableQ, where_prov_columnQ, where_prov_keyQ,

   dataQ, provQ, emptyProvQ

 ) where

import           Prelude       as P
import           Data.Default
import           Data.Text

import           Database.DSH.Frontend.Externals as D
import           Database.DSH.Frontend.Internals
import           Database.DSH.Provenance.Common

-- Provenance annotation selectors written by hand rather than derived with
-- generateTableSelectors, because generateTableSelectors cannot handle
-- polymorphic data types.
where_prov_tableQ :: (QA a) => Q (WhereProvAnnot a) -> Q Text
where_prov_tableQ (view -> (table_, _, _)) = table_

where_prov_columnQ :: (QA a) => Q (WhereProvAnnot a) -> Q Text
where_prov_columnQ (view -> (_, column, _)) = column

where_prov_keyQ :: (QA a) => Q (WhereProvAnnot a) -> Q a
where_prov_keyQ (view -> (_, _, key)) = key

whereProvToPair :: Q (WhereProv a key) -> Q (a, (Bool, WhereProvAnnot key))
whereProvToPair (Q a) = (Q a)

-- | Extract data component of where-provenance-annotated value
dataQ :: (QA a, QA key)
      => Q (WhereProv a key)
      -> Q (ProvData (WhereProv a key))
dataQ = D.fst . whereProvToPair

-- | Extract provenance component of where-provenance-annotated value
provQ :: (QA a, QA key, Default key)
      => Q (WhereProv a key)
      -> Q (ProvAnnot (WhereProv a key))
provQ = D.pairToMaybe . D.snd . whereProvToPair

-- | Attach empty where-provenance to a value
emptyProvQ :: forall a key. (QA a, QA key, Default key)
           => Q a
           -> Q (WhereProv a key)
-- Empty where-provenance is a NoProv constructor, which is represented
-- internally using a tuple with first component being False and the second
-- being some default value that is not intended to be used
emptyProvQ (Q a) = Q (TupleConstE (Tuple2E a
                      (TupleConstE (Tuple2E (BoolE False)
                                    (toExp (def :: WhereProvAnnot key))))))
