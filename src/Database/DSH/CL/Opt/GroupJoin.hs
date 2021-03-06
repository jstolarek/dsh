{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- FIXME TODO
-- * Use same infrastructure to introduce GroupAggr
-- * Special case: duplicate elimination -> CountDistinct

-- | Introduce GroupJoin operators for combinations of NestJoin and aggregation
-- of the groups created by NestJoin. This effectively fuses group creation and
-- aggregation and avoids materialization of the groups.
module Database.DSH.CL.Opt.GroupJoin
  ( groupjoinR
  , sidewaysR
  , optimizeGroupJoinR
  ) where

import           Control.Arrow

import           Data.List
import           Data.List.NonEmpty            (NonEmpty ((:|)))
import qualified Data.List.NonEmpty            as N
import qualified Data.Map                      as M
import           Data.Semigroup                ((<>))
import qualified Data.Set                      as S

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives    as P

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.FoldGroup


--------------------------------------------------------------------------------
-- Introduce GroupJoin operator for aggregates in the comprehension head or a
-- guard.

groupjoinR :: RewriteC CL
groupjoinR = mergegroupjoinHeadR <+ mergegroupjoinQualsR

-- | Merge a NestJoin operator and an aggregate into a GroupJoin. This rewrite
-- searches for eligible aggregates both in the comprehension head as well as in
-- any guards.
--
-- Unnesting from the head:
--
-- @
-- [ f (a [ g y | y <- x.2 ])
-- | x <- nestjoin{p} xs ys
-- , qs
-- ]
-- => (given that qs contains no further generators and there are no further occurences of x.2)
-- [ f[x.2/a [ g y | y <- x.2 ]]
-- | x <- groupjoin{p, [a(g(I))]} xs ys
-- , qs
-- ]
-- @
--
-- Unnesting from a guard:
--
-- @
-- [ h
-- | x <- nestjoin{p} xs ys
-- , qs
-- , f (a [ g y | y <- x.2 ])
-- , qs'
-- ]
-- => (given that qs contains no further generators and there are no further occurences of x.2)
-- [ h
-- | x <- groupjoin{p, [a(g(I))]} xs ys
-- , qs
-- ]
-- @
--
-- FIXME we propably do not need to restrict ourselves to one-generator
-- comprehensions. GroupJoin does not change the shape of the list produced by
-- NestJoin.
--
-- FIXME explicitly check that we have no further occurences of x.2
-- groupjoinR :: RewriteC CL
-- groupjoinR = logR "groupjoin.construct" $ do
--     Comp ty _ qs <- promoteT idR

--     -- We need one NestJoin generator on a comprehension
--     (x, p, xs, ys) <- case qs of
--         S (BindQ x (NestJoinP _ p xs ys))  -> return (x, p, xs, ys)
--         BindQ x (NestJoinP _ p xs ys) :* _ -> return (x, p, xs, ys)
--         _                                  -> fail "no match"

--     -- Search for an eligible aggregate in the comprehension head and guards.
--     (aggPath, agg) <- childT CompHead (searchAggregatedGroupT x)
--                       <+
--                       pathT [CompQuals, QualsTail] (traverseGuardsT x (searchAggregatedGroupT x))

--     let (joinOp, joinTy) = mkGroupJoin agg p xs ys
--         xv'              = Var joinTy x

--     localPath <- localizePathT aggPath

--     -- Replace the aggregate expression with x.2 (the aggregate produced by
--     -- GroupJoin).
--     Comp _ h' qs' <- pathR localPath (constT $ return $ inject $ P.snd xv') >>> projectT

--     -- Update the type of the variable bound by the NestJoin/GroupJoin
--     -- generator.
--     scopeNames <- inScopeNamesT
--     let (qs'', h'') = substCompE scopeNames x xv' qs' h'

--     case qs'' of
--         BindQ _ _ :* qsr -> return $ inject $ Comp ty h'' (BindQ x joinOp :* qsr)
--         S (BindQ _ _)    -> return $ inject $ Comp ty h'' (S (BindQ x joinOp))
--         _                -> $impossible


--------------------------------------------------------------------------------

-- | Side-ways information passing to pre-filter the left GroupJoin input in a
-- GroupJoin-NestJoin combination.
--
-- Basic idea: Execute the GroupJoin only for those elements of ys that will
-- actually find a join partner in the NestJoin. If the right child of a
-- NestJoin is a GroupJoin, we can not reorder the corresponding vector
-- operators. Consequently, the GroupJoin will be executed for all elements from
-- its left input, even if those will not match any elements in the outer left
-- input.
--
-- We attempt to ease this problem by applying a form of side-ways information
-- passing: Before performing the GroupJoin, its left input is filtered to
-- retain only those elements which will find a match in the outermost vector.
--
-- This rewrite triggers for example in regionsTopCustomers.
sidewaysR :: RewriteC CL
sidewaysR = logR "groupjoin.sideways" $ do
    NestJoinP ty1 p1 xs (GroupJoinP ty2 p2 as ys zs) <- promoteT idR
    guardM $ sidewaysCompatible p1
    let semiPred = sidewaysPred p1
    return $ inject $ NestJoinP ty1 p1 xs (GroupJoinP ty2 p2 as (SemiJoinP (typeOf ys) semiPred ys xs) zs)

-- | Check whether all right conjunct right sides refer only to the first tuple
-- component of the right input.
--
-- c_1 op c_2 with only I.1 in c_2
sidewaysCompatible :: JoinPredicate ScalarExpr -> Bool
sidewaysCompatible p = all firstOnly $ jcRight <$> jpConjuncts p

-- | Transform the nestjoin predicate for the semijoin:
-- c1 op c2
-- =>
-- c2[I/I.1] (flip op) c1
sidewaysPred :: JoinPredicate ScalarExpr -> JoinPredicate ScalarExpr
sidewaysPred (JoinPred cs) = JoinPred $ fmap updateConjunct cs
  where
    updateConjunct jc = JoinConjunct (untuplifyScalarExpr $ jcRight jc)
                                     (flipRelOp $ jcOp jc)
                                     (jcLeft jc)

--------------------------------------------------------------------------------

-- | Rewrite a GroupJoin that expresses an existential quantifier over a short
-- literal list into a regular disjunction expression.
--
-- @
-- groupjoin{e L == R, [any(True)]} xs [v1, ..., vn]
-- =>
-- [ (x, e x == v1 || ... || e x == vn) | x <- xs ]
-- @
--
-- For a short literal list, evaluating the simple expression will be
-- considerably more efficient than a GroupJoin, i.e. an OUTER JOIN followed by
-- GRP.
--
-- This rewrite is particularly helpful in TPC-H Q19.
disjunctiveGroupJoinR :: RewriteC CL
disjunctiveGroupJoinR = logR "groupjoin.disjunctive" $ do
    GroupJoinP _ (SingleJoinPredP ex Eq JInput{}) (NE (a :| [])) xs (LitListP (ListT litTy) (v:vs)) <- promoteT idR
    AggrApp Or (JLit _ (ScalarV (BoolV True))) <- return a
    guardM $ length vs < 30

    x <- freshNameT []
    let ex' = fromScalarExpr x ex
    let xTy = elemT $ typeOf xs
        resTy = TupleT [xTy, PBoolT]

    let disjunct l = P.scalarBinOp (SBRelOp Eq) ex' (Lit litTy l)
        disjunction = foldl' (\d l -> P.scalarBinOp (SBBoolOp Disj) (disjunct l) d) (disjunct v) vs
        headExpr = P.pair (Var xTy x) disjunction

    return $ inject $ Comp (ListT resTy) headExpr (S (x :<-: xs))

--------------------------------------------------------------------------------

optimizeGroupJoinR :: RewriteC CL
optimizeGroupJoinR = disjunctiveGroupJoinR <+ mergeGroupjoinR

--------------------------------------------------------------------------------
-- Initial Fold/Group fusion for aggregates in qualifiers

-- | Construct a groupjoin operator for the given inputs and predicate. Return
-- the operator expression and its element type.
mkGroupJoin :: AggrApp -> JoinPredicate ScalarExpr -> Expr -> Expr -> (Expr, [Type])
mkGroupJoin agg p xs ys =
    (GroupJoinP (ListT (TupleT joinElemTy)) p (pure agg) xs ys, joinElemTy)
  where
    xTy        = elemT $ typeOf xs
    aTy        = aggType agg
    joinElemTy = [xTy, aTy]

-- | Search qualifiers for a group generator that can be fused with aggregates
-- in subsequent qualifiers.
mergeGroupJoinSpineQualsT :: Expr -> TransformC CL (NL Qual, Expr)
mergeGroupJoinSpineQualsT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (NestJoinP ty p xs ys) :* _) ->
        do
            let joinElemTy = tupleElemTypes $ elemT ty
            (Just (gjName, agg), qsCl) <- statefulT Nothing
                                              $ childT QualsTail
                                              $ searchAggQualsR (take 1 joinElemTy) M.empty x
            let (gjOp, gjElemTy) = mkGroupJoin agg p xs ys
            scopeNames <- S.insert x <$> inScopeNamesT
            qs' <- constT $ projectM qsCl
            let (qs'', h') = substCompE scopeNames x (Var (TupleT gjElemTy) gjName) qs' h
            pure (BindQ gjName gjOp :* qs'', h')
        <+
        do
            (qs', h') <- childT QualsTail (mergeGroupJoinSpineQualsT h)
            pure (BindQ x (NestJoinP ty p xs ys) :* qs', h')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (mergeGroupJoinSpineQualsT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (mergeGroupJoinSpineQualsT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Introduce a new groupaggr operator by merging one particular aggregate from
-- the comprehension qualifiers into a group operator.
mergegroupjoinQualsR :: RewriteC CL
mergegroupjoinQualsR = logR "groupjoin.construct.quals" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ mergeGroupJoinSpineQualsT h
    pure $ inject $ Comp ty h' qs'

--------------------------------------------------------------------------------

-- | Search qualifiers for a group generator that can be fused with aggregates
-- in the head.
mergeGroupJoinSpineHeadT :: Expr -> TransformC CL (NL Qual, Expr)
mergeGroupJoinSpineHeadT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (NestJoinP ty p xs ys) :* qs) ->
        do
            let joinElemTy = tupleElemTypes $ elemT ty
            (Just (gjName, agg), h') <- statefulT Nothing
                                            $ childT QualsTail
                                            $ traverseToHeadT (take 1 joinElemTy) M.empty x h
            let (gjOp, gjElemTy) = mkGroupJoin agg p xs ys
            scopeNames <- S.insert x <$> inScopeNamesT
            let (qs', h'') = substCompE scopeNames x (Var (TupleT gjElemTy) gjName) qs h'
            pure (BindQ gjName gjOp :* qs', h'')
        <+
        do
            (qs', h') <- childT QualsTail (mergeGroupJoinSpineHeadT h)
            pure (BindQ x (NestJoinP ty p xs ys) :* qs', h')
    QualsCL (S (BindQ x (NestJoinP ty p xs ys))) -> do
        let joinElemTy = tupleElemTypes $ elemT ty
        ctx <- contextT
        let ctx' = ctx { clBindings = M.insert x (TupleT joinElemTy) (clBindings ctx) }
        (Just (gjName, agg), h') <- statefulT Nothing
                                        $ constT (pure $ inject h)
                                              >>> withContextT ctx' (searchAggExpR (take 1 joinElemTy) M.empty x)
                                              >>> projectT
        let (gjOp, gjElemTy) = mkGroupJoin agg p xs ys
        scopeNames <- S.insert x <$> inScopeNamesT
        let h'' = substE scopeNames x (Var (TupleT gjElemTy) gjName) h'
        pure (S (BindQ gjName gjOp), h'')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (mergeGroupJoinSpineHeadT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (mergeGroupJoinSpineHeadT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Introduce a new groupaggr operator by merging one particular aggregate from
-- the comprehension head into a group operator.
mergegroupjoinHeadR :: RewriteC CL
mergegroupjoinHeadR = logR "groupjoin.construct.head" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ mergeGroupJoinSpineHeadT h
    pure $ inject $ Comp ty h' qs'

--------------------------------------------------------------------------------
-- Merging of GroupJoin operators

-- | Check whether the join predicates of two stacked GroupJoins are compatible
-- for merging. They are compatible if the predicate of the topmost join refers
-- to the first tuple component of the left input and they are otherwise
-- identical.
leftCompatible :: ScalarExpr -> ScalarExpr -> Bool
leftCompatible (JBinOp op e1 e2) (JBinOp op' e1' e2') =
    op == op' && leftCompatible e1 e1' && leftCompatible e2 e2'
leftCompatible (JUnOp op e) (JUnOp op' e') =
    op == op' && leftCompatible e e'
leftCompatible (JLit _ v) (JLit _ v') =
    v == v'
leftCompatible (JTupElem First JInput{}) (JInput _) = True
leftCompatible (JTupElem n e) (JTupElem n' e') =
    n == n' && leftCompatible e e'
leftCompatible _ _ = False

-- | Merge two group joins into one if their join predicates and left inputs are
-- compatible.
mergeGroupjoinR :: RewriteC CL
mergeGroupjoinR = logR "groupjoin.merge" $ do
    GroupJoinP _ p1 (NE (a1 :| [])) (GroupJoinP ty p2 (NE as) xs ys) ys' <- promoteT idR
    guardM $ ys == ys'

    guardM $ and $ N.zipWith (\c1 c2 -> leftCompatible (jcLeft c1) (jcLeft c2)
                                        && jcOp c1 == jcOp c2
                                        && jcRight c1 == jcRight c2)
                             (jpConjuncts p1)
                             (jpConjuncts p2)

    mergeExistingAggrR a1 as (elemT ty) p2 xs ys <+ mergeNewAggrR a1 as p2 xs ys

-- | If the aggregate from the upper GroupJoin is already computed in the lower
-- GroupJoin, reuse that one.
mergeExistingAggrR :: AggrApp -> N.NonEmpty AggrApp -> Type -> JoinPredicate ScalarExpr -> Expr -> Expr -> RewriteC CL
mergeExistingAggrR a as ty p xs ys = do
    -- The argument expression of aggregate 'a' refers to the lower
    -- GroupJoin output tuples. We have to eliminate references to the first
    -- tuple component and change the type of the input accordingly.
    let xt  = elemT $ typeOf xs
        yt  = elemT $ typeOf ys
        a'  = a { aaArg = mapInput (const $ TupleT [xt, yt]) $ unFst (aaArg a) }

    Just aggIndex <- return $ elemIndex a' $ N.toList as
    let combinedJoin = GroupJoinP (ListT ty) p (NE as) xs ys

    ga <- freshNameT []
    let gav = Var ty ga

    let h = P.pair (P.tuple $ map (\i -> P.tupElem (intIndex i) gav) [1..length as + 1])
                   (P.tupElem (intIndex $ aggIndex + 2) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin

-- | Change a scalar expression that only refers to the first tuple component of
-- the input to refer directly to the input.
unFst :: ScalarExpr -> ScalarExpr
unFst (JIf e1 e2 e3)                             = JIf (unFst e1) (unFst e2) (unFst e3)
unFst (JBinOp op e1 e2)                          = JBinOp op (unFst e1) (unFst e2)
unFst (JUnOp op e)                               = JUnOp op (unFst e)
unFst (JTupElem First (JInput (TupleT [t1, _]))) = JInput t1
unFst (JTupElem i (JInput ty))                   = JTupElem i (JInput ty)
unFst (JTupElem idx e)                           = JTupElem idx (unFst e)
unFst (JLit ty val)                              = JLit ty val
unFst (JInput _)                                 = error "unFst"

-- | If the aggregate computed by the upper GroupJoin does not exist in the
-- lower GroupJoin, add it there and eliminate the upper GroupJoin.
mergeNewAggrR :: AggrApp -> N.NonEmpty AggrApp -> JoinPredicate ScalarExpr -> Expr -> Expr -> RewriteC CL
mergeNewAggrR a as p xs ys = do
    let xt  = elemT $ typeOf xs
        yt  = elemT $ typeOf ys
        a1t = aggType a
        ats = map aggType $ N.toList as
        gt  = TupleT $ xt : ats ++ [a1t]
        -- The argument expression of aggregate 'a' refers to the lower
        -- GroupJoin output tuples. We have to eliminate references to the first
        -- tuple component and change the type of the input accordingly.
        a'  = a { aaArg = mapInput (const $ TupleT [xt, yt]) $ unFst (aaArg a) }
        as' = as <> pure a'
        combinedJoin = GroupJoinP (ListT gt) p (NE as') xs ys

    ga <- freshNameT []
    let gav = Var gt ga

    let h = P.pair (P.tuple $ map (\i -> P.tupElem (intIndex i) gav) [1..length as + 1])
                   (P.tupElem (intIndex $ length as + 2) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin

