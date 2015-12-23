module Database.DSH.VL.Opt.Properties.TopDown
    ( inferTopDownProperties
    ) where

import           Control.Monad.State
import           Text.Printf

import qualified Data.IntMap                               as M

import qualified Database.Algebra.Dag                      as D
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Opt
import           Database.DSH.VL.Lang
import           Database.DSH.VL.Opt.Properties.ReqColumns
import           Database.DSH.VL.Opt.Properties.Types

reqColumnsSeed :: ReqCols
reqColumnsSeed = Nothing

vPropSeed :: TopDownProps
vPropSeed = TDProps { reqColumnsProp = VProp reqColumnsSeed }

vPropPairSeed :: TopDownProps
vPropPairSeed = TDProps { reqColumnsProp = VPropPair reqColumnsSeed reqColumnsSeed }

vPropTripleSeed :: TopDownProps
vPropTripleSeed = TDProps { reqColumnsProp = VPropTriple reqColumnsSeed
                                                         reqColumnsSeed
                                                         reqColumnsSeed }

seed :: VL -> TopDownProps
seed (NullaryOp _) = vPropSeed
seed (UnOp op _)   =
    case op of
        Nest               -> vPropPairSeed
        WinFun _           -> vPropSeed
        Reverse            -> vPropPairSeed
        ReverseS           -> vPropPairSeed
        UniqueS            -> vPropSeed
        UnboxKey           -> vPropSeed
        Unique             -> vPropSeed
        Segment            -> vPropSeed
        Select     _       -> vPropPairSeed
        Sort _             -> vPropPairSeed
        SortS _            -> vPropPairSeed
        Group _            -> vPropTripleSeed
        GroupS _           -> vPropTripleSeed
        Project      _     -> vPropSeed
        Aggr _             -> vPropSeed
        GroupAggr (_, _)   -> vPropSeed
        R1                 -> vPropSeed
        R2                 -> vPropSeed
        R3                 -> vPropSeed
        Number             -> vPropSeed
        NumberS            -> vPropSeed

seed (BinOp op _ _) =
    case op of
        Append       -> vPropTripleSeed
        AppendS      -> vPropTripleSeed
        ZipS         -> vPropTripleSeed
        DistLift     -> vPropPairSeed
        DistSng      -> vPropPairSeed
        AppKey       -> vPropPairSeed
        AppSort      -> vPropPairSeed
        AppFilter    -> vPropPairSeed
        AppRep       -> vPropPairSeed
        UnboxSng  -> vPropPairSeed
        AggrS _      -> vPropSeed
        Zip          -> vPropTripleSeed
        Align        -> vPropSeed
        CartProduct  -> vPropTripleSeed
        CartProductS -> vPropTripleSeed
        ThetaJoin _  -> vPropTripleSeed
        NestJoin _   -> vPropTripleSeed
        NestProduct  -> vPropTripleSeed
        ThetaJoinS _ -> vPropTripleSeed
        SemiJoin _   -> vPropPairSeed
        SemiJoinS _  -> vPropPairSeed
        AntiJoin _   -> vPropPairSeed
        AntiJoinS _  -> vPropPairSeed
        NestJoinS _  -> vPropTripleSeed
        GroupJoin _  -> vPropSeed
        NestProductS -> vPropTripleSeed

seed (TerOp op _ _ _) =
    case op of
        Combine -> vPropTripleSeed


type InferenceState = NodeMap TopDownProps

lookupProps :: AlgNode -> State InferenceState TopDownProps
lookupProps n = do
    m <- get
    case M.lookup n m of
        Just props -> return props
        Nothing -> error "TopDown.lookupProps"

replaceProps :: AlgNode -> TopDownProps -> State InferenceState ()
replaceProps n p = modify (M.insert n p)

inferUnOp :: BottomUpProps
          -> TopDownProps
          -> TopDownProps
          -> UnOp
          -> Either String TopDownProps
inferUnOp childBUProps ownProps cp op = do
    cols <- inferReqColumnsUnOp childBUProps
                                (reqColumnsProp ownProps)
                                (reqColumnsProp cp)
                                op
    return $ TDProps { reqColumnsProp = cols }

inferBinOp :: BottomUpProps
           -> BottomUpProps
           -> TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> BinOp
           -> Either String (TopDownProps, TopDownProps)
inferBinOp childBUProps1 childBUProps2 ownProps cp1 cp2 op = do
    (crc1', crc2') <- inferReqColumnsBinOp childBUProps1
                                           childBUProps2
                                           (reqColumnsProp ownProps)
                                           (reqColumnsProp cp1)
                                           (reqColumnsProp cp2) op
    let cp1' = TDProps { reqColumnsProp = crc1' }
        cp2' = TDProps { reqColumnsProp = crc2' }
    return (cp1', cp2')

inferTerOp :: TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> TopDownProps
           -> TerOp
           -> Either String (TopDownProps, TopDownProps, TopDownProps)
inferTerOp ownProps cp1 cp2 cp3 op = do
    (crc1', crc2', crc3') <- inferReqColumnsTerOp (reqColumnsProp ownProps)
                                                  (reqColumnsProp cp1)
                                                  (reqColumnsProp cp2)
                                                  (reqColumnsProp cp3) op
    let cp1' = TDProps { reqColumnsProp = crc1' }
        cp2' = TDProps { reqColumnsProp = crc2' }
        cp3' = TDProps { reqColumnsProp = crc3' }
    return (cp1', cp2', cp3')

inferChildProperties :: NodeMap BottomUpProps
                     -> D.AlgebraDag VL
                     -> AlgNode
                     -> State InferenceState ()
inferChildProperties buPropMap d n = do
    ownProps <- lookupProps n
    case D.operator n d of
        NullaryOp _ -> return ()
        UnOp op c -> do
            cp <- lookupProps c
            let buProps = lookupUnsafe buPropMap "TopDown.infer" c
            let cp' = checkError n [cp] d $ inferUnOp buProps ownProps cp op
            replaceProps c cp'
        BinOp op c1 c2 -> do
            cp1 <- lookupProps c1
            cp2 <- lookupProps c2
            let buProps1 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c1
                buProps2 = lookupUnsafe buPropMap "TopDown.inferChildProperties" c2
            let (cp1', cp2') = checkError n [cp1, cp2] d
                               $ inferBinOp buProps1 buProps2 ownProps cp1 cp2 op
            replaceProps c1 cp1'
            replaceProps c2 cp2'
        TerOp op c1 c2 c3 -> do
          cp1 <- lookupProps c1
          cp2 <- lookupProps c2
          cp3 <- lookupProps c3
          let (cp1', cp2', cp3') = checkError n [cp1, cp2, cp3] d
                                   $ inferTerOp ownProps cp1 cp2 cp3 op
          replaceProps c1 cp1'
          replaceProps c2 cp2'
          replaceProps c3 cp3'

checkError :: AlgNode -> [TopDownProps] -> D.AlgebraDag VL -> Either String p -> p
checkError n childProps d (Left msg) =
    let completeMsg   = printf "Inference failed at node %d\n%s\n%s\n%s"
                                n msg (show childProps) (show $ D.nodeMap d)
    in error completeMsg
checkError _ _ _ (Right props) = props

-- | Infer properties during a top-down traversal.
inferTopDownProperties :: NodeMap BottomUpProps
                       -> [AlgNode]
                       -> D.AlgebraDag VL
                       -> NodeMap TopDownProps
inferTopDownProperties buPropMap topOrderedNodes d = execState action initialMap
  where
    action = mapM_ (inferChildProperties buPropMap d) topOrderedNodes
    initialMap = M.map seed $ D.nodeMap d
