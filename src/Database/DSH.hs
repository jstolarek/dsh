-- | This module is intended to be imported @qualified@, to avoid name clashes
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
    ( module Database.DSH.Frontend.Externals
    , Q, QA, TA, Elim, elim, View, view, Key(..), TableHints(..), Emptiness(..)
    , Provenance(..)
    , module Database.DSH.Frontend.TH
    , module Database.DSH.Provenance
    , module Data.Proxy
    , module Data.String
    , module Data.Text
    , module Data.Decimal
    , module Data.Time.Calendar
    , module Prelude
    ) where

import Database.DSH.Frontend.Externals
import Database.DSH.Frontend.Internals (Q,QA,TA,Elim,elim,View,view,Key(..),TableHints(..), Emptiness(..), Provenance(..))
import Database.DSH.Frontend.TH
import Database.DSH.Provenance ( QLT(..) )

import Data.Proxy (Proxy)
import Data.String (IsString,fromString)
import Data.Text (Text)
import Data.Decimal (Decimal)
import Data.Time.Calendar (Day)
import Prelude hiding (
    not
  , (&&)
  , (||)
  , (==) , (/=)
  , (<)
  , (<=)
  , (>=)
  , (>)
  , (++)
  , mod
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
  , (++)
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
  , zip3
  , zipWith3
  , unzip3
  , fst
  , snd
  , maybe
  , either
  , return
  , (>>=)
  , (>>)
  , quot
  , rem
  )
