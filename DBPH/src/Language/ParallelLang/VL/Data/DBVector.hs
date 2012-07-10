{-# LANGUAGE DeriveGeneric #-}
module Language.ParallelLang.VL.Data.DBVector(DBCol, DBV(..), DBP(..), DescrVector(..), PropVector(..), RenameVector(..), AlgNode, GraphM) where

import Database.Algebra.Dag.Common
import Database.Algebra.Dag.Builder
import GHC.Generics (Generic)

type DBCol = Int

data DBV = DBV AlgNode [DBCol]
    deriving (Show, Generic)

data DBP = DBP AlgNode [DBCol] 
    deriving (Show, Generic)
    
data DescrVector = DescrVector AlgNode
    deriving (Generic)

data PropVector = PropVector AlgNode
    deriving (Generic)

data RenameVector = RenameVector AlgNode
    deriving (Generic)
