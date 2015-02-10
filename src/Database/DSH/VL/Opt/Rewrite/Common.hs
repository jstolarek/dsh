{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.VL.Opt.Rewrite.Common where

import qualified Data.IntMap                                   as M

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Impossible

import           Database.DSH.Common.Opt
import           Database.DSH.VL.Lang
import           Database.DSH.Common.Vector

import           Database.DSH.VL.Opt.Properties.BottomUp
import           Database.DSH.VL.Opt.Properties.TopDown
import           Database.DSH.VL.Opt.Properties.Types

  -- Type abbreviations for convenience
type VLRewrite p = Rewrite VL (Shape VLDVec) p
type VLRule p = Rule VL p (Shape VLDVec)
type VLRuleSet p = RuleSet VL p (Shape VLDVec)
type VLMatch p = Match VL p (Shape VLDVec)

inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  props <- infer inferBottomUpProperties
  return props

inferTopDown :: VLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to <- topsort
  buPropMap <- infer inferBottomUpProperties
  props <- infer (inferTopDownProperties buPropMap to)
  return props

inferProperties :: VLRewrite (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: AlgNode -> VLRewrite [AlgNode]
lookupR1Parents q = do
  let isR1 q' = do
        o <- operator q'
        case o of
          UnOp R1 _ -> return True
          _         -> return False

  ps <- parents q
  filterM isR1 ps

lookupR2Parents :: AlgNode -> VLRewrite [AlgNode]
lookupR2Parents q = do
  let isR2 q' = do
        o <- operator q'
        case o of
          UnOp R2 _ -> return True
          _         -> return False

  ps <- parents q
  filterM isR2 ps

mergeExpr :: [(DBCol, Expr)] -> Expr -> Expr
mergeExpr env expr =
    case expr of
        BinApp o e1 e2 -> BinApp o (mergeExpr env e1) (mergeExpr env e2)
        UnApp o e1     -> UnApp o (mergeExpr env e1)
        Column c       -> case lookup c env of
                               Just expr' -> expr'
                               Nothing    -> error $ show c ++ " " ++ show env
        If c t e       -> If (mergeExpr env c) (mergeExpr env t) (mergeExpr env e)
        Constant _     -> expr

-- | Unwrap a constant value
constVal :: Monad m => (VLVal -> a) -> ConstPayload -> m a
constVal wrap (ConstPL val) = return $ wrap val
constVal _             _    = fail "no match"

mapAggrFun :: (Expr -> Expr) -> AggrFun -> AggrFun
mapAggrFun f (AggrMax e) = AggrMax $ f e
mapAggrFun f (AggrSum t e) = AggrSum t $ f e
mapAggrFun f (AggrMin e) = AggrMin $ f e
mapAggrFun f (AggrAvg e) = AggrAvg $ f e
mapAggrFun f (AggrAny e) = AggrAny $ f e
mapAggrFun f (AggrAll e) = AggrAll $ f e
mapAggrFun _ AggrCount   = AggrCount

mapWinFun :: (Expr -> Expr) -> WinFun -> WinFun
mapWinFun f (WinMax e)        = WinMax $ f e
mapWinFun f (WinSum e)        = WinSum $ f e
mapWinFun f (WinMin e)        = WinMin $ f e
mapWinFun f (WinAvg e)        = WinAvg $ f e
mapWinFun f (WinAny e)        = WinAny $ f e
mapWinFun f (WinAll e)        = WinAll $ f e
mapWinFun f (WinFirstValue e) = WinFirstValue $ f e
mapWinFun _ WinCount          = WinCount

mapExprCols :: (DBCol -> DBCol) -> Expr -> Expr
mapExprCols f (BinApp op e1 e2) = BinApp op (mapExprCols f e1) (mapExprCols f e2)
mapExprCols f (UnApp op e)      = UnApp op (mapExprCols f e)
mapExprCols f (Column c)        = Column $ f c
mapExprCols _ (Constant val)    = Constant val
mapExprCols f (If c t e)        = If (mapExprCols f c) 
                                     (mapExprCols f t) 
                                     (mapExprCols f e)