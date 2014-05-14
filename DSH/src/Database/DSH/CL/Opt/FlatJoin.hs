{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Introduce simple equi joins.
module Database.DSH.CL.Opt.FlatJoin
  ( flatjoinsR
  ) where
  
import Control.Applicative
import Control.Arrow
import qualified Data.Map as M
import qualified Data.Set as S
       
import Database.DSH.Common.Lang
import Database.DSH.CL.Kure
import Database.DSH.CL.Lang
import Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------
-- Introduce simple theta joins

-- | Concstruct an equijoin generator
mkthetajoinT 
  :: Expr  -- ^ The predicate
  -> Ident -- ^ Identifier from the first generator
  -> Ident -- ^ Identifier from the second generator
  -> Expr  -- ^ First generator expression
  -> Expr  -- ^ Second generator expression
  -> Translate CompCtx TuplifyM (NL Qual) (RewriteC CL, Qual)
mkthetajoinT joinPred x y xs ys = do
    -- The predicate must be an equi join predicate
    joinConjunct <- constT (return joinPred) >>> (liftstateT $ splitJoinPredT x y)

    -- Conditions for the rewrite are fulfilled. 
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
        pt           = listT $ pairT xt yt
        jt           = xst .-> (yst .-> pt)
        tuplifyHeadR = tuplifyR x (x, xt) (y, yt)
        joinGen      = BindQ x 
                         (AppE2 pt 
                           (Prim2 (ThetaJoin (singlePred joinConjunct)) jt) 
                           xs ys)

    return (tuplifyHeadR, joinGen)

-- | Match an equijoin pattern in the middle of a qualifier list
eqjoinQualR :: Rewrite CompCtx TuplifyM (NL Qual)
eqjoinQualR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* GuardQ p :* qs <- promoteT idR
    
    (tuplifyHeadR, q') <- mkthetajoinT p x y xs ys
                               
    -- Next, we apply the tuplifyHeadR rewrite to the tail, i.e. to all following
    -- qualifiers
    -- FIXME why is extractT required here?
    qs' <- catchesT [ liftstateT $ (constT $ return qs) >>> (extractR tuplifyHeadR)
                    , constT $ return qs
                    ]            

    -- The tuplify rewrite must be handed to the top level
    constT $ put tuplifyHeadR
    
    return $ q' :* qs'
    
-- | Match an equijoin pattern at the end of a qualifier list
eqjoinQualEndR :: Rewrite CompCtx TuplifyM (NL Qual)
eqjoinQualEndR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* (S (GuardQ p)) <- promoteT idR

    (tuplifyHeadR, q') <- mkthetajoinT p x y xs ys

    -- The tuplify rewrite must be handed to the top level
    constT $ put tuplifyHeadR

    return (S q')

eqjoinQualsR :: Rewrite CompCtx TuplifyM (NL Qual) 
eqjoinQualsR = onetdR (eqjoinQualEndR <+ eqjoinQualR)
    
eqjoinR :: [Expr] -> [Expr] -> TranslateC CL (CL, [Expr], [Expr])
eqjoinR currentGuards testedGuards = do
    Comp t _ _          <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR eqjoinQualsR >>> projectT)
    e'                  <- (tryR $ childT CompHead tuplifyHeadR) >>> projectT
    -- FIXME should propably wrap tuplifyHeadR in tryR
    currentGuards'      <- constT (return currentGuards) >>> mapT (extractR tuplifyHeadR)
    testedGuards'       <- constT (return testedGuards) >>> mapT (extractR tuplifyHeadR)
    return $ (inject $ Comp t e' qs', currentGuards', testedGuards')

--------------------------------------------------------------------------------
-- Introduce semi joins (existential quantification)

-- | Construct a semijoin qualifier given a predicate and two generators
-- Note that the splitJoinPred call implicitly checks that only x and y
-- occur free in the predicate and no further correlation takes place.
mksemijoinT :: Expr -> Ident -> Ident -> Expr -> Expr -> TranslateC (NL Qual) Qual
mksemijoinT joinPred x y xs ys = do
    joinConjunct <- constT (return joinPred) >>> splitJoinPredT x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs semijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (SemiJoin $ singlePred joinConjunct) jt) xs ys)

-- | Match a IN semijoin pattern in the middle of a qualifier list
elemR :: RewriteC (NL Qual)
elemR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p 
                                                       (S (BindQ y ys)))) :* qs <- idR
    q' <- mksemijoinT p x y xs ys
    return $ q' :* qs

-- | Match a IN semijoin pattern at the end of a list
elemEndR :: RewriteC (NL Qual)
elemEndR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ] ]
    BindQ x xs :* (S (GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p
                                                           (S (BindQ y ys)))))) <- idR
    q' <- mksemijoinT p x y xs ys
    return (S q')
    
existentialQualsR :: RewriteC (NL Qual)
existentialQualsR = onetdR (elemR <+ elemEndR)

semijoinR :: RewriteC CL
semijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR existentialQualsR)

--------------------------------------------------------------------------------
-- Introduce anti joins (universal quantification)

--------------------------------------------------------------------------------
-- Basic antijoin pattern

-- | Construct an antijoin qualifier given a predicate and two generators. Note
-- that the splitJoinPred call implicitly checks that only x and y occur free in
-- the predicate and no further correlation takes place.
mkantijoinT :: Expr -> Ident -> Ident -> Expr -> Expr -> TranslateC (NL Qual) Qual
mkantijoinT joinPred x y xs ys = do
    joinConjunct <- constT (return joinPred) >>> splitJoinPredT x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs antijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (AntiJoin $ singlePred joinConjunct) jt) xs ys)

-- | Match the basic antijoin pattern in the middle of a qualifier list. This is
-- essentially the operator definition, generalized to multiple qualifiers and
-- an arbitrary comprehension head:
-- [ f x | qs, x <- xs, and [ not (q y) | y <- ys ], qs' ]
-- => [ f x | qs, x <- xs antijoin(q) ys, qs' ]
basicAntiJoinR :: RewriteC (NL Qual)
basicAntiJoinR = do
    -- [ ... | ..., x <- xs, and [ not p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 And _) 
                                  (Comp _ (UnOp _ (SUBoolOp Not) p)
                                          (S (BindQ y ys))))  :* qs <- idR
    q' <- mkantijoinT p x y xs ys
    return $ q' :* qs

-- | Match a NOT IN antijoin pattern at the end of a list
basicAntiJoinEndR :: RewriteC (NL Qual)
basicAntiJoinEndR = do
    -- [ ... | ..., x <- xs, and [ True | y <- ys, not p ] ]
    BindQ x xs :* S (GuardQ (AppE1 _ (Prim1 And _) 
                                     (Comp _ (UnOp _ (SUBoolOp Not) p)
                                             (S (BindQ y ys))))) <- idR
    q' <- mkantijoinT p x y xs ys
    return (S q')

--------------------------------------------------------------------------------
-- Doubly Negated existential quantifier (NOT EXISTS)

notinR :: RewriteC (NL Qual)
notinR = do
    BindQ x xs :* 
        (GuardQ (UnOp _ (SUBoolOp Not)
                         (AppE1 _ (Prim1 Or _)
                                  (Comp _ q (BindQ y ys :* (S (GuardQ p))))))) :* qs <- idR
                                  
    -- 
    
    q' <- mkClass15AntiJoinT x xs y ys p q
    return $ q' :* qs

notinEndR :: RewriteC (NL Qual)
notinEndR = do
    BindQ x xs :* 
        (S (GuardQ (UnOp _ (SUBoolOp Not)
                            (AppE1 _ (Prim1 Or _)
                                     (Comp _ q (BindQ y ys :* (S (GuardQ p)))))))) <- idR
                                  
    -- 
    
    q' <- mkClass15AntiJoinT x xs y ys p q
    return (S q')

--------------------------------------------------------------------------------
-- Universal quantification with range predicates
    
-- | Turn universal quantification with range and quantifier predicates into an
-- antijoin. We use the classification of queries in Claussen et al.: Optimizing
-- Queries with Universal Quantification in Object-Oriented and
-- Object-Relational Databases (VLDB 1995).
universalR :: RewriteC (NL Qual)
universalR = do
    -- [ ... | ..., x <- xs, and [ q y | y <- ys, p x y ], ... ]
    BindQ x xs :* (GuardQ (AppE1 _ (Prim1 And _)
                                   (Comp _ q ((BindQ y ys) :* (S (GuardQ p)))))) :* qs <- idR
                                   
    q' <- mkClass15AntiJoinT x xs y ys p q
    return $ q' :* qs
    
universalEndR :: RewriteC (NL Qual)
universalEndR = do
    -- [ ... | ..., x <- xs, and [ q y | y <- ys, p x y ] ]
    BindQ x xs :* (S (GuardQ (AppE1 _ (Prim1 And _)
                                      (Comp _ q ((BindQ y ys) :* (S (GuardQ p))))))) <- idR
                                      
    q' <- mkClass15AntiJoinT x xs y ys p q
    return (S q')

-- This rewrite implements plan 14 for Query Class 15 in Claussen et al.,
-- Optimizing Queries with Universal Quantification... (VLDB, 1995).  Class 15
-- contains queries in which the range predicate ranges over both relations,
-- i.e. x and y occur free. The quantifier predicate on the other hand ranges
-- only over the inner relation.
mkClass15AntiJoinT :: Ident -> Expr -> Ident -> Expr -> Expr -> Expr -> TranslateC (NL Qual) Qual
mkClass15AntiJoinT x xs y ys p q = do
    -- Check that the quantifier predicate only ranges over the inner relation
    guardM $ freeVars q == [y]
    
    -- The range predicate must have the form of a join predicate. This
    -- implicitly checks that the range predicate ranges over x and y.
    joinConjunct <- constT (return p) >>> splitJoinPredT x y
    
    let yst = typeOf ys
        yt  = elemT yst
    
    -- => [ ... | ..., x <- xs antijoin(p1, p2) [ y | y <- ys, not q ], ...]
    let ys' = Comp yst (Var yt y) (BindQ y ys :* (S (GuardQ (P.scalarUnOp (SUBoolOp Not) q))))
        q'  = BindQ x (P.antijoin xs ys' (singlePred joinConjunct))
    return q'

universalQualsR :: RewriteC (NL Qual)
universalQualsR = onetdR $ basicAntiJoinR 
                           <+ basicAntiJoinEndR 
                           <+ notinR
                           <+ notinEndR
                           <+ universalR 
                           <+ universalEndR

antijoinR :: RewriteC CL
antijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR universalQualsR)

------------------------------------------------------------------------
-- Flat join detection


-- | Try to build a join from a list of generators and a single
-- guard. If we can build an equi join, the remaining predicates must
-- be tuplified. For this reason, we pass them in here.
mkFlatJoin :: MergeGuard
mkFlatJoin comp guard guardsToTry leftOverGuards = do
    let C ty h qs = comp
    env <- S.fromList <$> M.keys <$> cl_bindings <$> contextT
    let comp' = ExprCL $ Comp ty h (insertGuard guard env qs)
    tryAntijoinR comp' <+ trySemijoinR comp' <+ tryEqjoinR comp'
    
  where
    tryAntijoinR :: CL -> TranslateC () (Comp, [Expr], [Expr])
    tryAntijoinR comp' = do
        ExprCL (Comp ty h qs') <- constT (return comp') >>> antijoinR
        return (C ty h qs', guardsToTry, leftOverGuards)

    trySemijoinR :: CL -> TranslateC () (Comp, [Expr], [Expr])
    trySemijoinR comp' = do
        ExprCL (Comp ty h qs') <- constT (return comp') >>> semijoinR
        return (C ty h qs', guardsToTry, leftOverGuards)

    tryEqjoinR :: CL -> TranslateC () (Comp, [Expr], [Expr])
    tryEqjoinR comp' = do
        res <- constT (return comp') >>> eqjoinR guardsToTry leftOverGuards
        (ExprCL (Comp ty h qs), guardsToTry', leftOverGuards') <- return res
        return (C ty h qs, guardsToTry', leftOverGuards')

flatjoinsR :: RewriteC CL
flatjoinsR = mergeGuardsIterR mkFlatJoin

