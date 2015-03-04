{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.Lang where

import           Control.Applicative
import           Data.Aeson
import           Data.Aeson.TH
import           Data.Decimal
import qualified Data.List.NonEmpty          as N

import           Database.Algebra.Dag        (Operator, opChildren,
                                              replaceOpChild)
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang    as L

data ScalarType = Int
                | Bool
                | Double
                | Decimal
                | String
                | Unit
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''ScalarType)

type VLColumn = (L.ColName, ScalarType)
type DBCol = Int

instance ToJSON Decimal where
    toJSON = toJSON . show

instance FromJSON Decimal where
    parseJSON s = read <$> parseJSON s

data VLVal = VLInt Int
           | VLBool Bool
           | VLString String
           | VLDouble Double
           | VLDecimal Decimal
           | VLUnit
           deriving (Eq, Ord, Show, Read)

$(deriveJSON defaultOptions ''VLVal)

data Expr = BinApp L.ScalarBinOp Expr Expr
          | UnApp L.ScalarUnOp Expr
          | Column DBCol
          | Constant VLVal
          | If Expr Expr Expr
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Expr)

-- | Helper function: Shift all column indexes in an expression by a certain offset.
shiftExprCols :: Int -> Expr -> Expr
shiftExprCols o (BinApp op e1 e2) = BinApp op (shiftExprCols o e1)
                                              (shiftExprCols o e2)
shiftExprCols o (UnApp op e)      = UnApp op (shiftExprCols o e)
shiftExprCols o (Column c)        = Column $ c + o
shiftExprCols _ (Constant v)      = Constant v
shiftExprCols o (If c t e)        = If (shiftExprCols o c)
                                       (shiftExprCols o t)
                                       (shiftExprCols o e)

data AggrFun = AggrSum ScalarType Expr
             | AggrMin Expr
             | AggrMax Expr
             | AggrAvg Expr
             | AggrAll Expr
             | AggrAny Expr
             | AggrCount
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
-- Vector Language operators. Documentation can be found in module
-- VectorPrimitives.

data NullOp = SingletonDescr
            | Lit (L.Emptiness, [ScalarType], [[VLVal]])
            | TableRef (String, [VLColumn], L.TableHints)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = UnboxRename
          | Segment
          | Unsegment

          | R1
          | R2
          | R3

          | Project [Expr]
          | Select Expr

          | GroupAggr ([Expr], N.NonEmpty AggrFun)
          | Aggr AggrFun
          | AggrNonEmpty (N.NonEmpty AggrFun)
          | AggrNonEmptyS (N.NonEmpty AggrFun)

          | Number
          | NumberS
          | UniqueS
          | Reverse
          | ReverseS
          | SelectPos1 (L.ScalarBinOp, Int)
          | SelectPos1S (L.ScalarBinOp, Int)
          | SortS [Expr]
          | GroupS [Expr]
          | WinFun (WinFun, FrameSpec)

          | Reshape Integer
          | ReshapeS Integer
          | Transpose
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = DistLift

           | PropRename
           | PropFilter
           | PropReorder

           | UnboxNested
           | UnboxScalar
           | Align

           | AggrS AggrFun
           | Append
           | AppendS
           | SelectPos L.ScalarBinOp
           | SelectPosS L.ScalarBinOp
           | Zip
           | ZipS
           | CartProduct
           | CartProductS
           | ThetaJoin (L.JoinPredicate Expr)
           | ThetaJoinS (L.JoinPredicate Expr)
           | SemiJoin (L.JoinPredicate Expr)
           | SemiJoinS (L.JoinPredicate Expr)
           | AntiJoin (L.JoinPredicate Expr)
           | AntiJoinS (L.JoinPredicate Expr)
           | NestJoin (L.JoinPredicate Expr)
           | NestJoinS (L.JoinPredicate Expr)
           | GroupJoin (L.JoinPredicate Expr, AggrFun)
           | NestProduct
           | NestProductS
           | TransposeS
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
