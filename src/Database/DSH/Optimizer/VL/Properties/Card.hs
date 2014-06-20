-- FIXME complete rules
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.Card where

import Control.Applicative

import Database.DSH.VL.Lang

import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.Common

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Card"

inferCardOneNullOp :: NullOp -> Either String (VectorProp Bool)
inferCardOneNullOp op =
  case op of
    SingletonDescr   -> Right $ VProp True
    Lit _ _ rows     -> Right $ VProp $ length rows == 1
    TableRef _ _ _   -> Right $ VProp False

inferCardOneUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferCardOneUnOp c op = 
  case op of
    UniqueS -> Right c
    Aggr _ -> Right $ VProp True
    AggrNonEmpty _ -> Right $ VProp True
    DescToRename -> Right c
    Segment -> Right c
    Unsegment -> Right c
    Project _  -> Right c
    Reverse -> unp c >>= (\uc -> return $ VPropPair uc uc)
    ReverseS -> unp c >>= (\uc -> return $ VPropPair uc uc)
    SelectPos1 _ _ -> Right $ VPropTriple False False False
    SelectPos1S _ _ -> Right $ VPropTriple False False False
    Select _ -> Right $ VPropPair False False
    SortScalarS _ -> unp c >>= (\uc -> return $ VPropPair uc uc)
    GroupScalarS _ -> unp c >>= (\uc -> return $ VPropTriple uc uc uc)
    R1 -> 
      case c of
        VProp _           -> Left "Properties.Card: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case c of
        VProp _           -> Left "Properties.Card: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case c of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.Card: not a triple"
    GroupAggr [] _ -> Right $ VProp True
    GroupAggr _ _  -> Right c
    Number -> Right c
    NumberS -> Right c
    Reshape _ -> unp c >>= (\uc -> return $ VPropPair uc uc)
    ReshapeS _ -> unp c >>= (\uc -> return $ VPropPair uc uc)
    Transpose -> unp c >>= (\uc -> return $ VPropPair uc uc)
    

inferCardOneBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> Either String (VectorProp Bool)
inferCardOneBinOp c1 c2 op =
  case op of
    GroupBy -> return $ VPropTriple False False False
    SortS -> return $ VPropPair False False
    AggrS _ -> return $ VProp False
    AggrNonEmptyS _ -> return $ VProp False
    DistPrim -> return $ VPropPair False False
    DistDesc -> return $ VPropPair False False
    Align -> return $ VPropPair False False
    PropRename -> return $ VProp False
    PropFilter -> return $ VPropPair False False
    PropReorder -> return $ VPropPair False False
    Unbox -> return $ VPropPair False False
    -- FIXME more precisely: empty(left) and card1(right) or card1(left) and empty(right)
    Append -> Right $ VPropTriple False False False
    AppendS -> Right $ VPropTriple False False False
    Restrict -> Right $ VPropPair False False
    SelectPos _ -> return $ VPropTriple False False False
    SelectPosS _ -> return $ VPropTriple False False False
    Zip -> VProp <$> ((||) <$> unp c1 <*> unp c2)
    CartProduct -> return $ VPropTriple False False False
    CartProductS -> return $ VPropTriple False False False
    NestProductS -> return $ VPropTriple False False False
    ThetaJoin _ -> return $ VPropTriple False False False
    ThetaJoinS _ -> return $ VPropTriple False False False
    NestJoinS _ -> return $ VPropTriple False False False
    SemiJoin _ -> return $ VPropPair False False
    SemiJoinS _ -> return $ VPropPair False False
    AntiJoin _ -> return $ VPropPair False False
    AntiJoinS _ -> return $ VPropPair False False
    TransposeS -> return $ VPropPair False False
    ZipS -> do
      c <- (||) <$> unp c1 <*> unp c2
      return $ VPropTriple c c c
      
inferCardOneTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferCardOneTerOp _ _ _ op =
  case op of
    Combine -> return $ VPropTriple False False False