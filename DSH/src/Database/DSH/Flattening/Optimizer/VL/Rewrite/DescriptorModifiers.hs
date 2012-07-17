{-# LANGUAGE TemplateHaskell #-}

module Optimizer.VL.Rewrite.DescriptorModifiers where

import Control.Monad

import qualified Data.Map as M

import Optimizer.VL.Properties.Types
import Optimizer.VL.Rewrite.Common

import Database.Algebra.Rewrite
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data
  
stripFromRoot :: DagRewrite VL Bool
stripFromRoot = iteratively $ preOrder inferBottomUp stripRootRules

stripRootRules :: RuleSet VL BottomUpProps
stripRootRules = [ stripFlatRootPropRename
                 , stripFlatRootPropRenameProject
                 , stripFlatRootSegment
                 , stripFlatRootSegmentProject ]
                 
schemaWidth :: VectorSchema -> Int
schemaWidth (ValueVector w) = w
schemaWidth _               = error "DescriptorModifiers.schemaWidth: non-ValueVector input"

stripFlatRootPropRename :: Rule VL BottomUpProps
stripFlatRootPropRename q =
  $(pattern [| q |] "(qp) PropRename (qv)"
    [| do
        rs <- rootNodes
        predicate $ (length rs) == 1
        predicate $ q `elem` rs
        width <- liftM (schemaWidth . vectorSchemaProp) $ properties $(v "qv")
        
        return $ do
          logRewriteM "DescriptorModifiers.FlatRootPropRename" q
          let valProjs = map Payload [1..width]
              projectOp = UnOp (ProjectValue (ConstCol (VLNat 1), PosCol, valProjs)) $(v "qv")
          replaceM q projectOp |])

-- FIXME duplicatin the rule like this to account for the introduced root projection is horrible.
-- Instead, the code should walk the DAG from the top rightwards, search for a chain of
-- descriptor modifiers and then remove the complete chain.
stripFlatRootPropRenameProject :: Rule VL BottomUpProps
stripFlatRootPropRenameProject q =
  $(pattern [| q |] "ProjectValue ps (qpr=(qp) PropRename (qv))"
    [| do
        let (descrProj, _, _) = $(v "ps")
        predicate $ case descrProj of
          ConstCol (VLNat 1) -> True
          _                  -> False
        rs <- rootNodes
        predicate $ (length rs) == 1
        predicate $ q `elem` rs
        
        return $ do
          logRewriteM "DescriptorModifiers.FlatRootPropRename" q
          valueOp <- operatorM $(v "qv")
          replaceM $(v "qpr") valueOp |])

stripFlatRootSegment :: Rule VL BottomUpProps
stripFlatRootSegment q =
  $(pattern [| q |] "Segment (qv)"
    [| do
        rs <- rootNodes
        predicate $ (length rs) == 1
        predicate $ q `elem` rs
        width <- liftM (schemaWidth . vectorSchemaProp) $ properties $(v "qv")
        
        return $ do
          logRewriteM "DescriptorModifiers.FlatRootSegment" q
          let valProjs = map Payload [1..width]
              projectOp = UnOp (ProjectValue (ConstCol (VLNat 1), PosCol, valProjs)) $(v "qv")
          replaceM q projectOp |])

stripFlatRootSegmentProject :: Rule VL BottomUpProps
stripFlatRootSegmentProject q =
  $(pattern [| q |] "ProjectValue ps (qs=Segment (qv))"
    [| do
        let (descrProj, _, _) = $(v "ps")
        predicate $ case descrProj of
          ConstCol (VLNat 1) -> True
          _                  -> False
        rs <- rootNodes
        predicate $ (length rs) == 1
        predicate $ q `elem` rs
        
        return $ do
          logRewriteM "DescriptorModifiers.FlatRootSegment" q
          valueOp <- operatorM $(v "qv")
          replaceM $(v "qs") valueOp |])