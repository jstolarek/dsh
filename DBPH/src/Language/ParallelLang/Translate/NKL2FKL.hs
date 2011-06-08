{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.NKL2FKL (flatTransform) where

import qualified Language.ParallelLang.FKL.Data.FKL as F
import qualified Language.ParallelLang.NKL.Data.NKL as N
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Config
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Impossible
import Language.ParallelLang.Common.Data.Type

import qualified Data.Set as S

import Control.Applicative

flatTransform :: N.Expr -> TransM (F.Expr Type)
flatTransform e = do
                           e'   <- withCleanLetEnv $ transform e
                           return e'

transEnv :: [(String, N.Expr)] -> TransM [(String, F.Expr Type)]
transEnv ((x, v):xs) = do
                        v' <- transform v
                        xs' <- transEnv xs
                        return ((x, v'):xs')
transEnv []          = return []

transform :: N.Expr -> TransM (F.Expr Type)
transform (N.Nil t) = pure $ F.Nil t
transform (N.App t e1 es) = cloApp t <$> transform e1 <*> mapM transform es
transform (N.Lam t arg e) = do
                             fvs <- transEnv $ S.toList $ freeVars (arg:topLevelVars) e
                             i' <- getFreshVar
                             n' <- getFreshVar
                             let n = F.Var (listT (Var "a")) n'
                             e' <- foldr withLetVar (flatten i' n e) (arg: map fst fvs)
                             e'' <- transform e
                             return $ F.Clo (funToCloTy t) n' fvs (F.Lam t arg e'') (F.Lam (liftType t) arg e')
transform (N.Let t n e1 e2) = F.Let t n <$> transform e1 <*> transform e2
transform (N.If t e1 e2 e3) = F.If t <$> transform e1 <*> transform e2 <*> transform e3
-- transform (N.BinOp _ (Op ":" 0) e1 e2) = error "TODO: desugar cons in nkl2fkl"
transform (N.BinOp t o e1 e2) = F.BinOp t o <$> transform e1 <*> transform e2
transform (N.Const t v) = pure $ F.Const t v
transform (N.Var t x) = pure $ F.Var t x
transform (N.Iter t n e1 e2) = do
                                let ty = unliftType (typeOf e1) .-> (typeOf e2)
                                let f  = N.Lam ty n e2
                                f' <- transform f
                                e1' <- transform e1
                                return $ cloLApp t (distF f' e1') [e1']  
transform (N.Proj t l e1 i) = flip (F.Proj t l) i <$> transform e1

flatten :: String -> F.Expr Type -> N.Expr -> TransM (F.Expr Type)
flatten _ e1 (N.Var t x) | x `elem` topLevelVars = return $ distF (F.Var t x) e1
                         | otherwise             = return $ F.Var (liftType t) x
flatten _ e1 (N.Const t v) = return $ distF (F.Const t v) e1
flatten _ e1 (N.Nil t) = return $ distF (F.Nil t) e1
flatten i e1 (N.App t f es) = cloLApp (liftType t) <$> flatten i e1 f <*> mapM (flatten i e1) es
flatten i d (N.Proj t 0 e1 el) = do
                                    e1' <- flatten i d e1
                                    return $ F.Proj (listT t) 1 e1' el
flatten _ _ (N.Proj _ _ _ _) = $impossible
flatten i d (N.Let ty v e1 e2) = do
                                    e1' <- flatten i d e1
                                    e2' <- withLetVar v $ flatten i d e2
                                    return $ F.Let (liftType ty) v e1' e2'
flatten i d (N.If _ e1 e2 e3) = do
                                    r1' <- getFreshVar
                                    r2' <- getFreshVar 
                                    v1' <- getFreshVar
                                    v2' <- getFreshVar
                                    v3' <- getFreshVar
                                    e1' <- flatten i d e1
                                    let v1 = F.Var (typeOf e1') v1'
                                    let rv1 = restrictF d v1
                                    let r1 = F.Var (typeOf rv1) r1'
                                    e2' <- flatten i r1 e2
                                    let rv2 = restrictF d (notF v1)
                                    let r2 = F.Var (typeOf rv2) r2'
                                    e3' <- flatten i r2 e3
                                    let v2 = F.Var (typeOf e2') v2'
                                    let v3 = F.Var (typeOf e3') v2'
                                    return $ letF v1' e1' $ letF r1' rv1 $ letF r2' rv2 $ letF v2' e2' $ letF v3' e3' $ combineF v1 v2 v3
-- flatten i d (N.BinOp _ (Op ":" 0) e1 e2) = undefined
flatten i d (N.BinOp t (Op o 0) e1 e2) = do
                                    (F.BinOp (liftType t) (Op o 1)) <$> flatten i d e1 <*> flatten i d e2
flatten _ _ (N.BinOp _ _ _ _) = $impossible
flatten v d (N.Lam t arg e) = do
                                i' <- getFreshVar
                                n' <- getFreshVar
                                let n = F.Var (typeOf d) n'
                                e' <- withCleanLetEnv $ transform e
                                fvs <- transEnv $ S.toList $ freeVars (arg:topLevelVars) e
                                e'' <- withCleanLetEnv $ foldr withLetVar (flatten i' n e) (arg: map fst fvs)
                                return $ letF v d $ F.AClo (liftType $ funToCloTy t) ((n', d):fvs) (F.Lam t arg e') (F.Lam (liftType t) arg e'')
flatten v d (N.Iter t n e1 e2) = do
                                    f <- withCleanLetEnv $ transform $ N.Lam (unliftType (typeOf e1) .-> typeOf e2) n e2
                                    e1' <- flatten v d e1
                                    return $ unconcatF e1' $ cloLApp t (concatF (distFL (distF f d) e1')) [concatF e1']