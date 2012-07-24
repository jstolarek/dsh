-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Database.DSH as Q
-- > import Database.DSH (Q)
--
-- Alternatively you can hide "Prelude" and import this module like this:
--
-- > import Prelude ()
-- > import Database.DSH
--
-- In this case you still get Prelude definitions that are not provided
-- by Database.DSH.

module Database.DSH
  (
    module Database.DSH.Combinators

    -- * Data Types
  , Q

    -- * Type Classes
  , QA
  , TA, table, tableDB, tableCSV, tableWithKeys, BasicType
  , View, view, fromView, tuple, record, caseOf, Case, gCurry

{-    -- * Template Haskell: Creating Table Representations
  , generateDatabaseRecordInstances
  , generateTableRecordInstances
  , generateRecordInstances
  , generateTableDeclarations
  , deriveQAConstructors -}

  , module Database.DSH.CSV
  , module Database.DSH.JSON
  , module Database.DSH.XHTML

  , module Data.String
  , module Data.Text
  , module Database.HDBC
  , module Prelude
  )
  where

import Database.DSH.Data (Q, QA, TA, table, tableDB, tableCSV, tableWithKeys, BasicType, View, view, fromView, tuple, record, caseOf, Case, gCurry)
-- import Database.DSH.TH (generateDatabaseRecordInstances, generateTableRecordInstances, generateRecordInstances, generateTableDeclarations)
import Database.DSH.DeriveConstructors

import Database.DSH.CSV
import Database.DSH.JSON
import Database.DSH.XHTML

import Database.DSH.Combinators

import Data.String(IsString,fromString)
import Data.Text (Text)
import Database.HDBC

import Prelude hiding (
    not
  , (&&)
  , (||)
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>=)
  , (>)
  , min
  , max
  , head
  , tail
  , take
  , drop
  , map
  , filter
  , last
  , init
  , null
  , length
  , (!!)
  , reverse
  , and
  , or
  , any
  , all
  , sum
  , concat
  , concatMap
  , maximum
  , minimum
  , splitAt
  , takeWhile
  , dropWhile
  , span
  , break
  , elem
  , notElem
  , lookup
  , zip
  , zipWith
  , unzip
  , fst
  , snd
  , maybe
  , either
  , return
  , (>>=)
  , (>>)
  )
