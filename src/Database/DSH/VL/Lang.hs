{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.Lang where

import           Data.Aeson.TH
import qualified Data.List.NonEmpty             as N
import           Data.Monoid
import qualified Data.Sequence                  as S

import           Database.Algebra.Dag           (Operator, opChildren,
                                                 replaceOpChild)
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Type


type DBCol = Int

data Expr = BinApp L.ScalarBinOp Expr Expr
          | UnApp L.ScalarUnOp Expr
          | Column DBCol
          | Constant L.ScalarVal
          | If Expr Expr Expr
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Expr)

data AggrFun = AggrSum ScalarType Expr
             | AggrMin Expr
             | AggrMax Expr
             | AggrAvg Expr
             | AggrAll Expr
             | AggrAny Expr
             | AggrCount
             | AggrCountDistinct Expr
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''AggrFun)

data WinFun = WinSum Expr
            | WinMin Expr
            | WinMax Expr
            | WinAvg Expr
            | WinAll Expr
            | WinAny Expr
            | WinFirstValue Expr
            | WinCount
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''WinFun)

-- | Specification of a window for the window aggregate operator.
data FrameSpec = -- | All elements up to and including the current
                 -- element are in the window
                 FAllPreceding
                 -- | All n preceding elements up to and including the
                 -- current one.
               | FNPreceding Int
                deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''FrameSpec)

--------------------------------------------------------------------------------
-- Segments for vector literals.

type Column = S.Seq L.ScalarVal

data Segment = Seg
    { segCols :: [Column]
    , segLen  :: !Int
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Segment)

newtype SegFrame = SegFrame { frameLen :: Int } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''SegFrame)

data Segments = UnitSeg [Column]
              | Segs [Segment]
              deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Segments)

-- | Extract complete columns from segments.
vectorCols :: [ScalarType] -> Segments -> [Column]
vectorCols tys (UnitSeg [])   = map (const S.empty) tys
vectorCols _   (UnitSeg cols) = cols
vectorCols tys (Segs segs)    = flattenSegments tys segs

flattenSegments :: [ScalarType] -> [Segment] -> [Column]
flattenSegments tys []   = map (const S.empty) tys
flattenSegments tys segs = go (map (const S.empty) tys) segs
  where
    go cols (s:ss) = go (zipWith (<>) cols (segCols s)) ss
    go cols []     = cols

--------------------------------------------------------------------------------
-- Vector Language operators. Documentation can be found in module
-- VectorAlgebra.

data NullOp = Lit ([ScalarType], SegFrame, Segments)
            | TableRef (String, L.BaseTableSchema)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = UnboxKey
          | Segment
          | Unsegment
          | Nest

          | R1
          | R2
          | R3

          | Project [Expr]
          | Select Expr

          | GroupAggr ([Expr], N.NonEmpty AggrFun)
          | Aggr AggrFun
          | NumberS
          | UniqueS
          | ReverseS
          | SortS [Expr]
          | GroupS [Expr]
          | WinFun (WinFun, FrameSpec)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = ReplicateNest
           | ReplicateScalar

           | AppKey
           | AppSort
           | AppFilter
           | AppRep

           | UnboxSng
           | Align

           | AggrS AggrFun
           | AppendS
           | ZipS
           | CartProductS
           | NestProductS
           | ThetaJoinS (L.JoinPredicate Expr)
           | SemiJoinS (L.JoinPredicate Expr)
           | AntiJoinS (L.JoinPredicate Expr)
           | NestJoinS (L.JoinPredicate Expr)
           | GroupJoin (L.JoinPredicate Expr, L.NE AggrFun)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

type VL = Algebra TerOp BinOp UnOp NullOp AlgNode

checkRep :: Eq a => a -> a -> a -> a
checkRep orig new x = if x == orig then new else x

instance Operator VL where
    opChildren (TerOp _ c1 c2 c3) = [c1, c2, c3]
    opChildren (BinOp _ c1 c2) = [c1, c2]
    opChildren (UnOp _ c) = [c]
    opChildren (NullaryOp _) = []

    replaceOpChild oper old new = replaceChild old new oper
      where
        replaceChild :: forall t b u n c. Eq c => c -> c -> Algebra t b u n c -> Algebra t b u n c
        replaceChild o n (TerOp op c1 c2 c3) = TerOp op (checkRep o n c1) (checkRep o n c2) (checkRep o n c3)
        replaceChild o n (BinOp op c1 c2) = BinOp op (checkRep o n c1) (checkRep o n c2)
        replaceChild o n (UnOp op c) = UnOp op (checkRep o n c)
        replaceChild _ _ (NullaryOp op) = NullaryOp op
