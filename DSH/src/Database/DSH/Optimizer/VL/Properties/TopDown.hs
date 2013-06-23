module Database.DSH.Optimizer.VL.Properties.TopDown(inferTopDownProperties) where

import Control.Monad.State
  
import qualified Data.IntMap as M

import Database.Algebra.Dag.Common
import Database.Algebra.Dag
import Database.Algebra.VL.Data

import Database.DSH.Optimizer.Common.Aux
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.ReqColumns
  
toDescrSeed :: Maybe Bool
toDescrSeed = Nothing
              
reqColumnsSeed :: ReqCols
reqColumnsSeed = Nothing

vPropSeed :: TopDownProps
vPropSeed = TDProps { reqColumnsProp = VProp reqColumnsSeed }

vPropPairSeed :: TopDownProps
vPropPairSeed = TDProps { reqColumnsProp = VPropPair reqColumnsSeed reqColumnsSeed }

vPropTripleSeed :: TopDownProps
vPropTripleSeed = TDProps { reqColumnsProp = VPropTriple reqColumnsSeed reqColumnsSeed reqColumnsSeed }
                  
seed :: VL -> TopDownProps
seed (NullaryOp _) = vPropSeed
seed (UnOp op _)   =
  case op of
    SelectPos1 _ _     -> vPropPairSeed
    SelectPos1L _ _    -> vPropPairSeed 
    ReverseA           -> vPropPairSeed
    ReverseL           -> vPropPairSeed
    Unique             -> vPropSeed
    UniqueL            -> vPropSeed
    NotPrim            -> vPropSeed
    NotVec             -> vPropSeed
    LengthA            -> vPropSeed
    DescToRename       -> vPropSeed
    Segment            -> vPropSeed
    Unsegment          -> vPropSeed
    VecSum _           -> vPropSeed
    VecAvg             -> vPropSeed
    VecMin             -> vPropSeed
    VecMinL            -> vPropSeed
    VecMax             -> vPropSeed
    VecMaxL            -> vPropSeed
    ProjectL _         -> vPropSeed
    ProjectA _         -> vPropSeed
    IntegerToDoubleA   -> vPropSeed
    IntegerToDoubleL   -> vPropSeed
    FalsePositions     -> vPropSeed
    SelectExpr _       -> vPropSeed
    ProjectRename _    -> vPropSeed
    ProjectAdmin _     -> vPropSeed
    ProjectPayload _   -> vPropSeed
    CompExpr1L _       -> vPropSeed
    VecAggr _ _        -> vPropSeed
    R1                 -> vPropSeed
    R2                 -> vPropSeed
    R3                 -> vPropSeed
    Only               -> undefined
    Singleton          -> undefined

seed (BinOp op _ _) = 
  case op of
    GroupBy            -> vPropTripleSeed
    Append             -> vPropTripleSeed
    ZipL               -> vPropTripleSeed
    SortWith           -> vPropPairSeed
    DistPrim           -> vPropPairSeed
    DistDesc           -> vPropPairSeed
    DistLift           -> vPropPairSeed
    PropFilter         -> vPropPairSeed
    PropReorder        -> vPropPairSeed
    RestrictVec        -> vPropPairSeed
    SelectPos _        -> vPropPairSeed
    SelectPosL _       -> vPropPairSeed
    LengthSeg          -> vPropSeed
    PropRename         -> vPropSeed
    CompExpr2 _        -> vPropSeed
    CompExpr2L _       -> vPropSeed
    VecSumL            -> vPropSeed
    VecAvgL            -> vPropSeed
    PairA              -> vPropSeed
    PairL              -> vPropSeed
    CartProduct        -> vPropTripleSeed
    CartProductL       -> vPropTripleSeed
    EquiJoin _ _       -> vPropTripleSeed
    EquiJoinL _ _      -> vPropTripleSeed
    
seed (TerOp op _ _ _) =
  case op of
    CombineVec -> vPropTripleSeed
    

type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> error "TopDown.lookupProps"

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: TopDownProps -> TopDownProps -> UnOp -> TopDownProps
inferUnOp ownProps cp op =
    TDProps { reqColumnsProp = inferReqColumnsUnOp (reqColumnsProp ownProps) (reqColumnsProp cp) op }

inferBinOp :: BottomUpProps 
              -> BottomUpProps
              -> TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> BinOp 
              -> (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op =
  let (crc1', crc2') = inferReqColumnsBinOp childBUProps1 childBUProps2 (reqColumnsProp ownProps) (reqColumnsProp cp1) (reqColumnsProp cp2) op
      cp1' = TDProps { reqColumnsProp = crc1' }
      cp2' = TDProps { reqColumnsProp = crc2' }
  in (cp1', cp2')

inferTerOp :: TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> TopDownProps 
              -> TerOp 
              -> (TopDownProps, TopDownProps, TopDownProps)
inferTerOp ownProps cp1 cp2 cp3 op =
  let (crc1', crc2', crc3') = inferReqColumnsTerOp (reqColumnsProp ownProps) (reqColumnsProp cp1) (reqColumnsProp cp2) (reqColumnsProp cp3) op
      cp1' = TDProps { reqColumnsProp = crc1' }
      cp2' = TDProps { reqColumnsProp = crc2' }
      cp3' = TDProps { reqColumnsProp = crc3' }
  in (cp1', cp2', cp3')

inferChildProperties :: NodeMap BottomUpProps -> AlgebraDag VL -> AlgNode -> State InferenceState ()
inferChildProperties buPropMap d n = do
    ownProps <- lookupProps n
    case operator n d of
        NullaryOp _ -> return ()
        UnOp op c -> do
            cp <- lookupProps c
            let cp' = inferUnOp ownProps cp op
            replaceProps c cp'
        BinOp op c1 c2 -> do
            cp1 <- lookupProps c1
            cp2 <- lookupProps c2
            let buProps1 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
                buProps2 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c2
            let (cp1', cp2') = inferBinOp buProps1 buProps2 ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> do
          cp1 <- lookupProps c1
          cp2 <- lookupProps c2
          cp3 <- lookupProps c3
          let (cp1', cp2', cp3') = inferTerOp ownProps cp1 cp2 cp3 op
          replaceProps c1 cp1'
          replaceProps c2 cp2'
          replaceProps c3 cp3'
    
-- | Infer properties during a top-down traversal.
inferTopDownProperties :: NodeMap BottomUpProps -> [AlgNode] -> AlgebraDag VL -> NodeMap TopDownProps
inferTopDownProperties buPropMap topOrderedNodes d = execState action initialMap 
    where action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes
          initialMap = M.map seed $ nodeMap d
          