{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt.NestJoin
  ( nestjoinHeadR
  , nestjoinGuardR
  , combineNestJoinsR 
  ) where
  
import           Debug.Trace
       
import           Control.Applicative((<$>))
import           Control.Arrow

import           Data.Either

import qualified Data.Foldable as F

import           Data.List.NonEmpty(NonEmpty((:|)), (<|))
import qualified Data.List.NonEmpty as N

import           Database.DSH.Impossible

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

import qualified Database.DSH.CL.Primitives as P

import           Database.DSH.CL.Opt.Aux

--------------------------------------------------------------------------------
-- Pulling out expressions from comprehension heads 

type HeadExpr = Either PathC (PathC, Type, Expr, NL Qual) 

-- | Collect expressions which we would like to replace in the comprehension
-- head: occurences of the variable bound by the only generator as well as
-- comprehensions nested in the head. We collect the expressions themself as
-- well as the paths to them.
collectExprT :: Ident -> TranslateC CL [HeadExpr] 
collectExprT x = prunetdT (collectVar <+ collectComp <+ blockLambda)
  where
    -- | Collect a variable if it refers to the name we are looking for
    collectVar :: TranslateC CL [HeadExpr]
    collectVar = do
        Var _ n <- promoteT idR
        guardM $ x == n
        path <- snocPathToPath <$> absPathT
        return [Left path]
    
    -- | Collect a comprehension and don't descend into it
    collectComp :: TranslateC CL [HeadExpr]
    collectComp = do
        Comp t h qs <- promoteT idR
        -- FIXME check here if the comprehension is eligible for unnesting?
        path <- snocPathToPath <$> absPathT
        return [Right (path, t, h, qs)]
        
    -- | don't descend past lambdas which shadow the name we are looking for
    blockLambda :: TranslateC CL [HeadExpr]
    blockLambda = do
        Lam _ n _ <- promoteT idR
        guardM $ n == x
        return []
        
-- | Apply a function n times
ntimes :: Int -> (a -> a) -> a -> a
ntimes 0 _ x = x
ntimes n f x = ntimes (n - 1) f (f x)

-- | Tuple accessor for position pos in left-deep tuples
tupleAt :: Expr -> Int -> Int -> Expr
tupleAt expr len pos = 
  case pos of
      p | p == 1             -> ntimes (len - 1) P.fst expr
      p | 2 <= p && p <= len -> P.snd $ ntimes (len - p) P.fst expr
      _                      -> $impossible                         
        
-- | Take an absolute path and drop the prefix of the path to a direct child of
-- the current node. This makes it a relative path starting from **some** direct
-- child of the current node.
dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix prefix xs = drop (1 + length prefix) xs

-- | Construct a left-deep tuple from at least two expressions
mkTuple :: Expr -> NonEmpty Expr -> Expr
mkTuple e1 es = F.foldl1 P.pair (e1 <| es)

constExprT :: Monad m => Expr -> Translate c m CL CL
constExprT expr = constT $ return $ inject expr
        
-- | Factor out expressions from a single-generator comprehension head, such
-- that only (pairs of) the generator variable and nested comprehensions in the
-- head remain. Beware: This rewrite /must/ be combined with a rewrite that
-- makes progress on the comprehension. Otherwise, a loop might occur when used
-- in a top-down fashion.
factoroutHeadR :: RewriteC CL
factoroutHeadR = do factoroutEndR <+ factoroutR
  where 
    factoroutEndR :: RewriteC CL
    factoroutEndR = do
        curr@(Comp t h (S (BindQ x xs))) <- promoteT idR
        -- debugUnit "factoroutEndR at" curr
        mkheadmapR curr t h x xs []
        
    factoroutR :: RewriteC CL
    factoroutR = do
        curr@(Comp t h ((BindQ x xs) :* qs)) <- promoteT idR

        -- Currently, we only allow additional guards, not qualifiers.
        -- FIXME this might be extendable to additional qualifiers
        guardM $ all isGuard (toList qs)
        -- debugUnit "factoroutR at" curr

        mkheadmapR curr t h x xs (toList qs)

mkheadmapR 
  :: Expr          -- ^ The current comprehension
  -> Type          -- ^ Type of the current comprehension
  -> Expr          -- ^ Comprehension head
  -> Ident         -- ^ Variable bound by the generator
  -> Expr          -- ^ Generator source
  -> [Qual]        -- ^ Possible additional guards
  -> RewriteC CL
mkheadmapR curr t h x xs qs = do


    -- Collect interesting expressions from the comprehension head 
    (vars, comps) <- partitionEithers <$> (oneT $ collectExprT x)

    -- We abort if we did not find any interesting comprehensions in the head
    guardM $ not $ null comps
    
    -- debugUnit "mkheadmapR found" (vars, comps)

    pathPrefix <- rootPathT

    let varTy = elemT $ typeOf xs

        varExpr   = if null vars 
                    then [] 
                    else [(Var varTy x, map (dropPrefix pathPrefix) vars)]

        -- Reconstruct comprehension expressions from the collected fragments
        compExprs = map (\(p, t', h', qs') -> (Comp t' h' qs', [dropPrefix pathPrefix p])) comps
        
        exprs     = varExpr ++ compExprs
        
    -- trace ("collected: " ++ show (varExpr ++ compExprs)) $ return ()
    -- trace ("currently at: " ++ show curr ++ " --- " ++ show pathPrefix) $ return ()
        
    (mapBody, h', headTy) <- case exprs of
              -- If there is only one interesting expression (which must be a
              -- comprehension), we don't need to construct tuples.
              [(comp@(Comp _ _ _), [path])] -> do
                  let lamVarTy = typeOf comp

                  -- Replace the comprehension with the lambda variable
                  mapBody <- (oneT $ pathR path (constT $ return $ inject $ Var lamVarTy x)) >>> projectT

                  return (mapBody, comp, lamVarTy)

              -- If there are multiple expressions, we construct a left-deep tuple
              -- and replace the original expressions in the head with the appropriate
              -- tuple constructors.
              es@(e1 : e2 : er)    -> do
                  let -- Construct a tuple from all interesting expressions
                      headTuple      = mkTuple (fst e1) (fmap fst $ e2 :| er)

                      lamVarTy       = typeOf headTuple
                      lamVar         = Var lamVarTy x
                      
                      -- Map all paths to a tuple accessor for the tuple we
                      -- constructed for the comprehension head
                      tupleAccessors = zipWith (\paths i -> (tupleAt lamVar (length es) i, paths))
                                               (map snd es)
                                               [1..]
                                               
                      
                      -- For each path, construct a rewrite to replace the
                      -- original expression at this path with the tuple
                      -- accessor
                      rewritePerPath = [ pathR path (constExprT ta) 
                                       | (ta, paths) <- tupleAccessors
                                       , path <- paths ]
                                       
                  mapBody <- (oneT $ serialise rewritePerPath) >>> projectT
                  return (mapBody, headTuple, lamVarTy)

              _            -> $impossible
              
    let qs' = case fromList qs of
                  Just qsTail -> (BindQ x xs) :* qsTail
                  Nothing     -> S (BindQ x xs)
              
    let lamTy = headTy .-> (elemT t)
    return $ inject $ P.map (Lam lamTy x mapBody) (Comp (listT headTy) h' qs')

------------------------------------------------------------------
-- Nestjoin introduction: unnesting in a comprehension head
    
-- FIXME this should work on left-deep tuples
tupleComponentsT :: TranslateC CL (NonEmpty Expr)
tupleComponentsT = do
    AppE2 _ (Prim2 Pair _) _ _ <- promoteT idR
    N.reverse <$> descendT
    
  where
    descendT :: TranslateC CL (NonEmpty Expr)
    descendT = descendPairT <+ singleT
    
    descendPairT :: TranslateC CL (NonEmpty Expr)
    descendPairT = do
        AppE2 _ (Prim2 Pair _) _ e <- promoteT idR
        tl <- childT 0 descendT
        return $ e <| tl
        
    singleT :: TranslateC CL (NonEmpty Expr)
    singleT = (:| []) <$> (promoteT idR)

    
-- | Base case for nestjoin introduction: consider comprehensions in which only
-- a single inner comprehension occurs in the head.
unnestHeadBaseT :: TranslateC CL Expr
unnestHeadBaseT = singleCompEndT <+ singleCompT <+ varCompPairT <+ varCompPairEndT
  where
    mknestjoinT 
      :: Type    -- ^ Type of the outer comprehension
      -> Type    -- ^ Type of the inner comprehension
      -> Expr    -- ^ Head of the inner comprehension
      -> Ident   -- ^ Variable for the inner generator
      -> Expr    -- ^ Source for the inner generator
      -> Expr    -- ^ Inner predicate
      -> Ident   -- ^ Outer generator variable
      -> Expr    -- ^ Outer generator source
      -> [Qual]  -- ^ Possibly additional outer qualifiers
      -> TranslateC CL Expr
    mknestjoinT t1 t2 h y ys p x xs preds = do
        -- Split the join predicate
        (leftExpr, rightExpr) <- constT (return p) >>> splitJoinPredT x y
        
        let xt       = elemT $ typeOf xs
            yt       = elemT $ typeOf ys
            tupType  = pairT xt (listT yt)
            joinType = listT xt .-> (listT yt .-> listT tupType)
            joinVar  = Var tupType x
            
        -- In the head of the inner comprehension, replace x with (snd x)
        h' <- constT (return h) >>> (extractR $ tryR $ substR x (P.fst joinVar))

        -- the nestjoin operator combining xs and ys: 
        -- xs nj(p) ys
        let xs'        = AppE2 (listT tupType) (Prim2 (NestJoin leftExpr rightExpr) joinType) xs ys

            headComp = case h of
                -- The simple case: the inner comprehension looked like [ y | y < ys, p ]
                -- => We can remove the inner comprehension entirely
                Var _ y' | y == y' -> P.snd joinVar
                
                -- The complex case: the inner comprehension has a non-idenity
                -- head: 
                -- [ h | y <- ys, p ] => [ h[fst x/x] | y <- snd x ] 
                -- It is safe to re-use y here, because we just re-bind the generator.
                _               -> Comp t2 h' (S $ BindQ y (P.snd joinVar))

        preds' <- constT (return $ map inject preds) 
                  >>> mapT (tryR $ substR x (P.fst joinVar))
                  >>> mapT projectT

        let qs = case fromList preds' of
                     Just npreds -> (BindQ x xs') :* npreds
                     Nothing     -> S (BindQ x xs')
                
        return $ Comp t1 headComp qs

    -- The base case: a single comprehension nested in the head of the outer
    -- comprehension. Assume only a single outer qualifier here.
    -- [ [ h y | y <- ys, p ] | x <- xs ]
    singleCompEndT :: TranslateC CL Expr
    singleCompEndT = do
        q@(Comp _ _ _) <- promoteT idR
        -- debugUnit "singleCompEndT at" (q :: Expr)

        -- [ [ h | y <- ys, p ] | x <- xs ]
        Comp t1 (Comp t2 h ((BindQ y ys) :* (S (GuardQ p)))) (S (BindQ x xs)) <- promoteT idR
        debug "trigger singleCompEndT" q $ mknestjoinT t1 t2 h y ys p x xs []
        
    -- The base case: a single comprehension nested in the head of the outer
    -- comprehension. Assume more than one outer qualifier here. However, we
    -- are conservative and expect only predicates as additional qualifiers
    -- here. This could propably be extended to more generators, as long as
    -- those generators do not bind variables which occur free in the inner
    -- comprehension.
    -- [ [ h y | y <- ys, p ] | x <- xs ]
    singleCompT :: TranslateC CL Expr
    singleCompT = do
    
        q@(Comp _ _ _) <- promoteT idR
        -- debugUnit "singleCompT at" (q :: Expr)

        -- [ [ h | y <- ys, p ] | x <- xs, qs ]
        Comp t1 (Comp t2 h ((BindQ y ys) :* (S (GuardQ p)))) ((BindQ x xs) :* qs) <- promoteT idR
        
        guardM $ all isGuard $ toList qs
        
        mknestjoinT t1 t2 h y ys p x xs (toList qs)

    -- The head of the outer comprehension consists of a pair of generator
    -- variable and inner comprehension
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    varCompPairEndT :: TranslateC CL Expr
    varCompPairEndT = do
        Comp _ (AppE2 _ (Prim2 Pair _) (Var _ x) _) (S (BindQ x' _)) <- promoteT idR

        guardM $ x == x'
        
        -- Reduce to the base case, then unnest, then patch the variable back in
        (removeVarR <+ removeVarEndR) >>> injectT >>> (singleCompEndT <+ singleCompT) >>> arr (patchVar x)

    varCompPairT :: TranslateC CL Expr
    varCompPairT = do
        Comp _ (AppE2 _ (Prim2 Pair _) (Var _ x) _) ((BindQ x' _) :* qs) <- promoteT idR
        
        guardM $ x == x'

        -- Only allow guards as additional qualifiers
        guardM $ all isGuard (toList qs)

        -- Reduce to the base case, then unnest, then patch the variable back in
        (removeVarR <+ removeVarEndR) >>> injectT >>> (singleCompEndT <+ singleCompT) >>> arr (patchVar x)
        
    -- Support rewrite: remove the variable from the outer comprehension head
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    -- => [ [ h y | y <- ys, p ] | x <- xs ]
    removeVarEndR :: TranslateC CL Expr
    removeVarEndR = do
        Comp _ (AppE2 t (Prim2 Pair _) (Var _ x) comp) (S (BindQ x' xs)) <- promoteT idR
        guardM $ x == x'
        let t' = listT $ sndT t
        return $ Comp t' comp (S (BindQ x xs))

    -- Support rewrite: remove the variable from the outer comprehension head
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    -- => [ [ h y | y <- ys, p ] | x <- xs ]
    removeVarR :: TranslateC CL Expr
    removeVarR = do
        Comp _ (AppE2 t (Prim2 Pair _) (Var _ x) comp) ((BindQ x' xs) :* qs) <- promoteT idR

        guardM $ x == x'

        -- Only allow guards as additional qualifiers
        guardM $ all isGuard (toList qs)

        let t' = listT $ sndT t
        return $ Comp t' comp ((BindQ x xs) :* qs)

patchVar :: Ident -> Expr -> Expr
patchVar x c =
    case c of
        Comp _ e qs@(S (BindQ x' je)) | x == x'    -> patch e je qs
        Comp _ e qs@((BindQ x' je) :* _) | x == x' -> patch e je qs
        _                                          -> $impossible
        
  where 
    patch :: Expr -> Expr -> (NL Qual) -> Expr
    patch e je qs =
        let joinBindType = elemT $ typeOf je
            e'           = P.pair (P.fst (Var joinBindType x)) e
            resultType   = listT $ pairT (fstT joinBindType) (typeOf e)
        in Comp resultType e' qs

unnestHeadR :: RewriteC CL
unnestHeadR = simpleHeadR <+ tupleHeadR

  where 
    simpleHeadR :: RewriteC CL
    simpleHeadR = do
        unnestHeadBaseT >>> injectT

    tupleHeadR :: RewriteC CL
    tupleHeadR = do
        -- e <- promoteT idR
        -- debugUnit "tupleHeadR at" (e :: Expr)
        Comp _ _ qs <- promoteT idR
  
        headExprs <- oneT tupleComponentsT 
        -- debugUnit "tupleHeadR collected" headExprs
        
        let mkSingleComp :: Expr -> Expr
            mkSingleComp expr = Comp (listT $ typeOf expr) expr qs
            
            headExprs' = case headExprs of
                v@(Var _ _) :| (comp : comps) -> P.pair v comp :| comps
                comps                         -> comps
                
            singleComps = fmap mkSingleComp headExprs'
            
        -- debugUnit "tupleheadR singleComps" singleComps
            
        -- FIXME fail if all translates failed -> define alternative to mapT
        unnestedComps <- constT (return singleComps) >>> mapT (injectT >>> unnestHeadBaseT)
        
        return $ inject $ F.foldl1 P.zip unnestedComps
        
nestjoinHeadR :: RewriteC CL
nestjoinHeadR = do
    c@(Comp _ _ _) <- promoteT idR
    -- debugUnit "nestjoinR at" c
    unnestHeadR <+ (factoroutHeadR >>> childR 1 unnestHeadR)

--------------------------------------------------------------------------------
-- Nestjoin introduction: unnesting comprehensions from complex predicates

-- | Try to unnest comprehensions from guards, which we can not unnest otherwise
-- (e.g. by introduing semi- or antijoins).
-- 
--   [ e | qs, x <- xs, p x e', qs' ] with e' = [ f x y | y <- ys, q x y ]
-- 
-- rewrites into
--
--   [ e[fst x/x] | qs, x <- xs nestjoin(q) ys, p[fst x/x][c/e'], qs'[fst x/x]
-- 
-- with
--
--   c = [ fst x/x] | y <- snd x ]
nestjoinGuardR :: RewriteC CL
nestjoinGuardR = do
    c@(Comp t _ _)         <- promoteT idR 
    -- debugUnit "nestjoinGuardR at" c
    (tuplifyHeadR, qs') <- statefulT idR 
                           $ childT 1 (anytdR (promoteR (unnestQualsEndR <+ unnestQualsR)) 
                                       >>> projectT)
                                       
    h'                  <- childT 0 tuplifyHeadR >>> projectT
    return $ inject $ Comp t h' qs'
    
  where
  
    unnestGuardT :: Ident -> Expr -> TranslateC Expr (RewriteC CL, Expr, Expr)
    unnestGuardT x xs = do
    
        e <- idR
        -- debugUnit "unnestGuard at" (e :: Expr)
        -- FIXME passing x is not necessary since we are not interested in
        -- collecting variables.
        -- Collect exactly one comprehension from the predicate.
        (_, [(path, t, f, qs)]) <- partitionEithers <$> extractT (collectExprT x)
        -- debugUnit "unnestGuardT collected" (path, t, f, qs)
        
        -- Check the shape of the inner qualifier list
        BindQ y ys :* (S (GuardQ q))  <- return qs
        
        -- Do we have a join predicate?
        (leftExpr, rightExpr)         <- constT (return q) >>> splitJoinPredT x y
        
        let xt       = elemT $ typeOf xs
            yt       = elemT $ typeOf ys
            tupType  = pairT xt (listT yt)
            joinType = listT xt .-> (listT yt .-> listT tupType)
            joinVar  = Var tupType x
            
            -- The nestjoin combining xs and ys
            xs'      = AppE2 (listT tupType) (Prim2 (NestJoin leftExpr rightExpr) joinType) 
                             xs 
                             ys
            
            tuplifyHeadR = substR x (P.fst joinVar)
            
        pathPrefix <- rootPathT
        let relPath = dropPrefix pathPrefix path
        
        -- debugUnit "pathPrefix, path, relPath" (pathPrefix, path, relPath)

        -- Substitute the body of the guard comprehension. As x might not occur,
        -- we need to guard the call.
        f' <- tryR $ constT (return $ inject f) >>> tuplifyHeadR >>> projectT
        
        -- debugUnit "f'" f'

        let c = Comp t f' (S (BindQ y (P.snd joinVar)))
        
        -- p[fst x/x][c/e'] 

        -- FIXME this looks a bit fragile. Actually, the tuplify substitution
        -- should not kill the path to the comprehension, but it would be better
        -- to be sure about this.
        p' <- injectT
              >>> tuplifyHeadR 
              >>> anyR (pathR relPath (constT (return $ inject c))) 
              >>> projectT
              
        -- debugUnit "p'" p'
        
        return (tuplifyHeadR, xs', p')
        
    unnestQualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    unnestQualsEndR = do
        c@(BindQ x xs :* (S (GuardQ p))) <- idR
        -- debugUnit "qualsEndR at" c
        (tuplifyHeadR, xs', p') <- liftstateT $ constT (return p) >>> unnestGuardT x xs
        -- debugUnit "qualsEndR (1)" xs'
        constT $ modify (>>> tuplifyHeadR)
        return $ BindQ x xs' :* (S (GuardQ p'))

    unnestQualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    unnestQualsR = do
        BindQ x xs :* GuardQ p :* qs <- idR
        (tuplifyHeadR, xs', p') <- liftstateT $ constT (return p) >>> unnestGuardT x xs
        constT $ modify (>>> tuplifyHeadR)
        qs' <- liftstateT $ constT (return $ inject qs) >>> tuplifyHeadR >>> projectT
        return $ BindQ x xs' :* GuardQ p' :* qs'
        
    
---------------------------------------------------------------------------------
-- Support rewrites which are specific to nestjoin introduction (i.e. cleaning
-- up the remains)

-- | Clean up a pattern left by nestjoin introduction (nested comprehension head)
-- 
-- zip [ f | x <- xs △_p1 ys, qs1 ]
--     [ g | x <- xs △_p2 zs, qs2 ]
--
-- =>
-- 
-- [ pair f[fst x/x] g[fst (fst x)/fst x]
-- | x <- (xs △_p1 ys) △_p2' zs
-- , qs[fst x/x]
-- ]
--
-- Soundness of this rewrite can be motivated by the following fact: |xs △ ys| = |xs|

combineNestJoinsR :: RewriteC CL
combineNestJoinsR = do
    AppE2 tz (Prim2 Zip _) (Comp tc1 f qs) (Comp tx2 g qs') <- promoteT idR
    
    case (qs, qs') of
        ( S (BindQ x xsys@(AppE2 _ (Prim2 (NestJoin _ _) _) xs ys)),
          S (BindQ x' (AppE2 _ (Prim2 (NestJoin p1 p2) _) xs' zs)))       -> do

            guardM $ x == x'
            guardM $ xs == xs'
            inject <$> fst <$> combineCompsT x xsys zs f g p1 p2
              
        ( (BindQ x xsys@(AppE2 _ (Prim2 (NestJoin _ _) _) xs ys)) :* qgs,
          (BindQ x' (AppE2 _ (Prim2 (NestJoin p1 p2) _) xs' zs)) :* qgs') -> do

            guardM $ x == x'
            guardM $ xs == xs'
            guardM $ qgs == qgs'

            (Comp t h (S q), tuplifyxR) <- combineCompsT x xsys zs f g p1 p2
            qgs' <- constT (return $ inject qgs) >>> tuplifyxR >>> projectT
            return $ inject $ Comp t h (q :* qgs')
          
        (_, _) ->
            fail "no match" 

  where
  
    combineCompsT
      :: Ident 
      -> Expr 
      -> Expr
      -> Expr
      -> Expr
      -> JoinExpr
      -> JoinExpr
      -> TranslateC CL (Expr, RewriteC CL)
    combineCompsT x xsys zs f g p1 p2 = do
        -- We need to change the left join predicate of the outer nestjoin,
        -- because the type of its input changed (from xs to nj(xs, ys)
        let p1'      = substJoinExpr p1
            -- The nestjoin between nj(xs, ys) and zs
            joinExpr = P.nestjoin xsys zs p1' p2
            qs       = S (BindQ x joinExpr)

           -- The element type of the combined nestjoin
            xt   = typeOf joinExpr
        
            xVar = Var xt x

            -- f[fst x/x]
            tuplifyxR = substR x (P.fst xVar)

        f' <- constT (return $ inject f) >>> tuplifyxR >>> projectT
        
        -- g[fst (fst x)/fst x]
        g' <- constT (return $ inject g) >>> (tryR $ anybuR $ replaceFstR x xt) >>> projectT

        -- Combine head expressions from both comprehensions by pairing them
        let h = P.pair f' g'
            
        return (Comp (listT $ typeOf h) h qs, tuplifyxR)
        
    replaceFstR :: Ident -> Type -> RewriteC CL
    replaceFstR x xt = do
        AppE1 _ (Prim1 Fst _) (Var _ x') <- promoteT idR
        guardM $ x == x'
        return $ inject $ P.fst $ P.fst $ Var xt x
        
    -- | Change all occurences of the join input in the predicate into accesses
    -- to the first tuple component of the input
    substJoinExpr :: JoinExpr -> JoinExpr
    substJoinExpr (BinOpJ op e1 e2) = BinOpJ op (substJoinExpr e1) (substJoinExpr e2)
    substJoinExpr (UnOpJ op e1)     = UnOpJ op (substJoinExpr e1)
    substJoinExpr (ConstJ v)        = ConstJ v
    substJoinExpr InputJ            = UnOpJ FstJ InputJ
