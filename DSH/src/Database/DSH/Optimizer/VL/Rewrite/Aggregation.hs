{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Aggregation(groupingToAggregation) where
       
import Debug.Trace
       
import Control.Applicative
import Control.Monad

import Database.Algebra.VL.Data
import Database.Algebra.Dag.Common

import Database.DSH.Impossible

import Database.DSH.Optimizer.Common.Rewrite
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Rewrite.Common

aggregationRules :: VLRuleSet ()
aggregationRules = [ inlineAggrProject
                   , flatGrouping
                   ]

aggregationRulesBottomUp :: VLRuleSet BottomUpProps
aggregationRulesBottomUp = [ pushExprThroughGroupBy
                           ]

groupingToAggregation :: VLRewrite Bool
groupingToAggregation = iteratively $ sequenceRewrites [ applyToAll inferBottomUp aggregationRulesBottomUp
                                                       , applyToAll noProps aggregationRules
                                                       ]

-- | If an expression operator is applied to the R2 output of GroupBy,
-- push the expression below the GroupBy operator. This rewrite
-- assists in turning combinations of GroupBy and Vec* into a form
-- that is suitable for rewriting into a VecAggr form. Even if this is
-- not possible, the rewrite should not do any harm
pushExprThroughGroupBy :: VLRule BottomUpProps
pushExprThroughGroupBy q = 
  $(pattern 'q "Project projs (qr2=R2 (qg=(qc) GroupBy (qp)))"
    [| do
        [e] <- return $(v "projs")
        case e of
          Column1 _ -> fail "no match"
          _         -> return ()
        
        -- get vector type of right grouping input to determine the
        -- width of the vector
        VProp (ValueVector w) <- vectorTypeProp <$> properties $(v "qp")
        
        return $ do
          logRewrite "Aggregation.Normalize.PushProject" q
          -- Introduce a new column below the GroupBy operator which contains
          -- the expression result
          let proj = map Column1 [1 .. w] ++ [e]
          projectNode <- insert $ UnOp (Project proj) $(v "qp")
          
          -- Link the GroupBy operator to the new projection
          groupNode   <- replaceWithNew $(v "qg") $ BinOp GroupBy $(v "qc") projectNode
          r2Node      <- replaceWithNew $(v "qr2") $ UnOp R2 groupNode
          
          -- Replace the CompExpr1L operator with a projection on the new column
          void $ replaceWithNew q $ UnOp (Project [Column1 $ w + 1]) r2Node |])

-- | Merge a projection into an aggregate operator if the projection
-- merely selects the column.
inlineAggrProject :: VLRule ()
inlineAggrProject q =
  $(pattern 'q "(qo) AggrS afun (Project proj (qi))"
    [| do
        [Column1 origCol] <- return $(v "proj")
        let afun' = case $(v "afun") of
                        AggrMax _   -> AggrMax origCol
                        AggrSum t _ -> AggrSum t origCol
                        AggrMin _   -> AggrMin origCol
                        AggrAvg _   -> AggrAvg origCol
                        AggrCount   -> AggrCount

        return $ do
            logRewrite "Aggregation.Normalize.InlineProject" q
            void $ replaceWithNew q $ BinOp (AggrS afun') $(v "qo") $(v "qi") |])

          
-- | Check if we have an operator combination which is eligible for moving to a
-- GroupAggr operator.
matchAggr :: AlgNode -> VLMatch () (AggrFun, AlgNode)
matchAggr q = do
  BinOp (AggrS aggrFun) _ _ <- getOperator q
  return (aggrFun, q)
  
projectionCol :: Expr1 -> VLMatch () DBCol
projectionCol (Column1 c) = return c
projectionCol _           = fail "no match"

          
-- We rewrite a combination of GroupBy and aggregation operators into a single
-- VecAggr operator if the following conditions hold: 
--
-- 1. The R2 output of GroupBy is only consumed by aggregation operators (MaxL, 
--    MinL, VecSumL, LengthSeg)
-- 2. The grouping criteria is a simple column projection from the input vector
flatGrouping :: VLRule ()
flatGrouping q =
  $(pattern 'q "R2 (qg=(Project ps (q1)) GroupBy (q2))"
    [| do
        -- FIXME this collides with pushProjectThroughGroupBy, as
        -- there will be a projection underneath the groupby operator
        -- predicate $ $(v "q1") == $(v "q2")
       
        -- We ensure that all parents of the groupBy are operators which we can
        -- turn into aggregate functions
        groupByParents <- getParents q
        funs <- mapM matchAggr groupByParents
        
        -- Check if the grouping criteria are simple columns. Extract the
        -- grouping cols from the left GroupBy input
        groupingCols <- mapM projectionCol $(v "ps")
        
        return $ do
          logRewrite "Aggregation.GroupingToAggr" q
          -- The output format of the new VecAggr operator is 
          -- [p1, ..., pn, a1, ..., am] where p1, ..., pn are the 
          -- grouping columns and a1, ..., am are the aggregates 
          -- themselves.
        
          -- We obviously assume that the grouping columns are still present in
          -- the right input of GroupBy at the same position. In combination
          -- with rewrite pushExprThroughGroupBy, this is true since we only
          -- add columns at the end.
          aggrNode <- insert $ UnOp (GroupAggr groupingCols (map fst funs)) $(v "q2")

          -- For every aggregate function, generate a projection which only
          -- leaves the aggregate column. Function receives the node of the
          -- original aggregate operator and the column in which the respective 
          -- aggregation result resides.
          let insertAggrProject :: AlgNode -> DBCol -> VLRewrite ()
              insertAggrProject oldAggrNode aggrCol = 
                void $ replaceWithNew oldAggrNode $ UnOp (Project [Column1 aggrCol]) aggrNode

          zipWithM_ insertAggrProject (map snd funs) [1 .. length funs]
          
          -- If the R1 output (that is, the vector which contains the grouping
          -- columns and desribes the group shape) of GroupBy is referenced, we
          -- replace it with a projection on the new VecAggr node.
          r1s <- lookupR1Parents $(v "qg")
          if length r1s > 0
            then do
              r1ProjectNode <- insert $ UnOp (Project (map Column1 [1 .. length groupingCols])) aggrNode
              mapM_ (\r1 -> replace r1 r1ProjectNode) r1s
            else return () |])

