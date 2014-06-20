module Database.DSH.VL.VectorPrimitives where

import qualified Data.List.NonEmpty              as N
import           Database.DSH.Common.Lang
import           Database.DSH.VL.Vector
import           Database.DSH.VL.Lang
import           Database.Algebra.Dag.Build

{-

FIXME
consistent naming scheme:

- atom = A
- lifted is the standard case
- difference between lifted and segmented -> segmented S
- common prefix: vec. vl is reserved for the actual VL operators
-}

class VectorAlgebra a where
    -- | A vector with one segment
    singletonDescr :: Build a DVec

    -- | A vector representing a literal list.
    vecLit :: [VLType] -> [[VLVal]] -> Build a DVec

    -- | A reference to a database-resident table.
    vecTableRef :: String -> [VLColumn] -> TableHints -> Build a DVec

    -- | Perform duplicate elimination per segment.
    vecUniqueS :: DVec -> Build a DVec

    -- | /Materialize/ vector positions. The operator adds an item
    -- column that contains the dense positions of the vector's
    -- elements.
    vecNumber :: DVec -> Build a DVec

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumberS :: DVec -> Build a DVec

    descToRename :: DVec -> Build a RVec

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: DVec -> Build a DVec

    vecUnsegment :: DVec -> Build a DVec

    vecAggr :: AggrFun -> DVec -> Build a DVec
    vecAggrS :: AggrFun -> DVec -> DVec -> Build a DVec
    vecAggrNonEmpty :: N.NonEmpty AggrFun -> DVec -> Build a DVec
    vecAggrNonEmptyS :: N.NonEmpty AggrFun -> DVec -> DVec -> Build a DVec

    -- | SelectPos filters a vector positionally as specified by the
    -- comparison operator and the position value from the right
    -- input. Next to the filtered value vector it produces two rename
    -- vectors:
    --
    -- * Mapping old to new positions (for re-aligning inner vectors)
    -- * Mapping old positions to segment descriptors (for unboxing one
    -- inner segment)
    vecSelectPos :: DVec -> ScalarBinOp -> DVec -> Build a (DVec, RVec, RVec)

    -- | Filter a vector positionally /by segment/. The right input
    -- vector provides a position offset /for each segment/. The
    -- operator produces the same triple of vectors as its non-segmented
    -- variant.
    vecSelectPosS :: DVec -> ScalarBinOp -> DVec -> Build a (DVec, RVec, RVec)

    -- | Filter a vector positionally on a /constant/ position.
    vecSelectPos1 :: DVec -> ScalarBinOp -> Nat -> Build a (DVec, RVec, RVec)

    -- | Filter a vector positionally based on a /constant
    -- position/. The operator filters by segment, but the constant
    -- position argument is the same for all segments.
    vecSelectPos1S :: DVec -> ScalarBinOp -> Nat -> Build a (DVec, RVec, RVec)

    -- | Reverse a vector.
    vecReverse :: DVec -> Build a (DVec, PVec)

    -- | Reverse each segment of a vector individually.
    vecReverseS :: DVec -> Build a (DVec, PVec)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: Expr -> DVec -> Build a (DVec, RVec)

    -- | General vector sorting (segmented). The sorting key is
    -- provided by the first input vector.
    vecSortS :: DVec -> DVec -> Build a (DVec, PVec)

    -- | Specialized variant of sorting: The sorting key is provided
    -- by a scalar expression.
    vecSortScalarS :: [Expr] -> DVec -> Build a (DVec, PVec)

    vecGroupBy :: DVec -> DVec -> Build a (DVec, DVec, PVec)
    vecGroupScalarS :: [Expr] -> DVec -> Build a (DVec, DVec, PVec)

    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: [Expr] -> DVec -> Build a DVec

    -- | The VL aggregation operator groups the input vector by the
    -- given columns and then performs the list of aggregations
    -- described by the second argument. The result is a flat vector,
    -- since all groups are reduced via aggregation. The operator
    -- operates segmented, i.e. always groups by descr first. This
    -- operator must be used with care: It does not determine the
    -- complete set of descr value to check for empty inner lists.
    vecGroupAggr :: [Expr] -> N.NonEmpty AggrFun -> DVec -> Build a DVec

    -- FIXME is distprim really necessary? could maybe be replaced by distdesc
    vecDistPrim :: DVec -> DVec -> Build a (DVec, PVec)
    vecDistDesc :: DVec -> DVec -> Build a (DVec, PVec)
    vecAlign    :: DVec -> DVec -> Build a (DVec, PVec)

    -- | propRename uses a propagation vector to rename a vector (no
    -- filtering or reordering).
    vecPropRename :: RVec -> DVec -> Build a DVec

    -- | propFilter uses a propagation vector to rename and filter a
    -- vector (no reordering).
    vecPropFilter :: RVec -> DVec -> Build a (DVec, RVec)

    -- | propReorder uses a propagation vector to rename, filter and
    -- reorder a vector.
    vecPropReorder :: PVec -> DVec -> Build a (DVec, PVec)

    -- | Specialized unbox operator that merges DescrToRename
    -- and PropRename. It takes an inner and outer vector, and
    -- pulls the segment that is referenced by the outer vector
    -- into the outer segment. Notice that there must be
    -- /exactly one/ segment referenced by the outer
    -- vector. Inner segments that are not referenced are
    -- silently discarded.
    --
    -- Output: @(DVec, RVec)@
    vecUnbox :: RVec -> DVec -> Build a (DVec, RVec)

    vecAppend :: DVec -> DVec -> Build a (DVec, RVec, RVec)
    vecAppendS :: DVec -> DVec -> Build a (DVec, RVec, RVec)

    vecRestrict :: DVec -> DVec -> Build a (DVec, RVec)

    -- | Positionally align two vectors. Basically: @zip xs ys@
    vecZip :: DVec -> DVec -> Build a DVec

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZipS :: DVec -> DVec -> Build a (DVec, RVec, RVec)

    vecCartProduct :: DVec -> DVec -> Build a (DVec, PVec, PVec)
    vecCartProductS :: DVec -> DVec -> Build a (DVec, PVec, PVec)
    vecNestProductS :: DVec -> DVec -> Build a (DVec, PVec)

    vecThetaJoin :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, PVec, PVec)
    vecThetaJoinS :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, PVec, PVec)
    vecNestJoinS :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, PVec)

    vecSemiJoin :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, RVec)
    vecSemiJoinS :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, RVec)

    vecAntiJoin :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, RVec)
    vecAntiJoinS :: JoinPredicate Expr -> DVec -> DVec -> Build a (DVec, RVec)

    vecCombine :: DVec -> DVec -> DVec -> Build a (DVec, RVec, RVec)

    -- | Experimental: @reshape m@ partitions a vector of length @n*m@
    -- into @n@ vectors of length @m@.
    --
    -- reshapeS can be computed only on the inner vector. As its
    -- result is one list nesting level deeper, it computes the new
    -- innermost vector from the old inner vector and then derives
    -- from that a 'middle' descriptor vector which represents lists
    -- at nesting depth 1.
    vecReshape :: Integer -> DVec -> Build a (DVec, DVec)

    -- | Experimental: segmented version of reshape.
    vecReshapeS :: Integer -> DVec -> Build a (DVec, DVec)

    -- | Experimental: Matrix transposition
    vecTranspose :: DVec -> Build a (DVec, DVec)

    -- | Experimental: Segmented matrix transposition
    vecTransposeS :: DVec -> DVec -> Build a (DVec, DVec)
