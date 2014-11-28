{-# LANGUAGE TemplateHaskell #-}
-- | The Flattening Transformation
module Database.DSH.Translate.NKL2FKL (flatTransform) where

-- FIXME use more let bindings to avoid term replication, e.g. in if conditionals
-- FIXME make sure that no wrong shadowing occurs while lifting or restricting the environment.

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative
import           Data.List.NonEmpty          (NonEmpty(..), (<|))

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Type
import qualified Database.DSH.FKL.Lang       as F
import qualified Database.DSH.FKL.Primitives as P
import           Database.DSH.FKL.Rewrite
import qualified Database.DSH.NKL.Lang       as N

-- | Transform an expression in the Nested Kernel Language into its
-- equivalent Flat Kernel Language expression by means of the
-- flattening transformation.
flatTransform :: N.Expr -> F.FExpr
flatTransform expr = optimizeFKL "FKL" 
                     $ normalize 
                     $ optimizeFKL "FKL Intermediate" 
                     $ runFlat [] (flatten expr)

--------------------------------------------------------------------------------
-- The Flattening Transformation

--------------------------------------------------------------------------------
-- Translation of built-in combinators. Combinators are lifted
-- according to the iteration depth at which they are encountered.

prim1 :: N.Prim1 -> F.LExpr -> Nat -> F.LExpr
prim1 p =
    case p of
        N.Singleton -> P.sng
        N.Length    -> P.length
        N.Concat    -> P.concat
        N.Sum       -> P.sum
        N.Avg       -> P.avg
        N.The       -> P.the
        N.TupElem n -> P.tupElem n
        N.Head      -> P.head
        N.Tail      -> P.tail
        N.Minimum   -> P.minimum
        N.Maximum   -> P.maximum
        N.Reverse   -> P.reverse
        N.And       -> P.and
        N.Or        -> P.or
        N.Init      -> P.init
        N.Last      -> P.last
        N.Nub       -> P.nub
        N.Number    -> P.number
        N.Reshape n -> P.reshape n
        N.Transpose -> P.transpose

prim2 :: N.Prim2 -> F.LExpr -> F.LExpr -> Nat -> F.LExpr
prim2 p =
    case p of
        N.Group        -> P.group
        N.Sort         -> P.sort
        N.Restrict     -> P.restrict
        N.Append       -> P.append
        N.Index        -> P.index
        N.Zip          -> P.zip
        N.CartProduct  -> P.cartProduct
        N.NestProduct  -> P.nestProduct
        N.ThetaJoin jp -> P.thetaJoin jp
        N.NestJoin jp  -> P.nestJoin jp
        N.SemiJoin jp  -> P.semiJoin jp
        N.AntiJoin jp  -> P.antiJoin jp

--------------------------------------------------------------------------------

type Flatten e a = Reader e a

runFlat :: e -> Flatten e a -> a
runFlat env ma = runReader ma env

envVar :: (Ident, Type) -> F.LExpr
envVar (n, t) = F.Var t n

ctxVarM :: (e -> (Ident, Type)) -> Flatten e F.LExpr
ctxVarM p = envVar <$> asks p

type LetEnv = [(Ident, Type)]

bindLetEnv :: Ident -> Type -> LetEnv -> LetEnv
bindLetEnv n t e = (n, t) : e

-- | Transform top-level expressions which are not nested in a
-- comprehension.
flatten :: N.Expr -> Flatten LetEnv F.LExpr
flatten (N.Table t n cs hs)  = return $ F.Table t n cs hs
flatten (N.UnOp t op e1)     = P.un t op <$> flatten e1 <*> pure Zero
flatten (N.BinOp t op e1 e2) = P.bin t op <$> flatten e1 <*> flatten e2 <*> pure Zero
flatten (N.Const t v)        = return $ F.Const t v
flatten (N.Var t v)          = return $ F.Var t v
flatten (N.If t ce te ee)    = F.If t <$> flatten ce <*> flatten te <*> flatten ee
flatten (N.AppE1 _ p e)      = prim1 p <$> flatten e <*> pure Zero
flatten (N.AppE2 _ p e1 e2)  = prim2 p <$> flatten e1 <*> flatten e2 <*> pure Zero
flatten (N.Let _ x xs e)     = P.let_ x <$> flatten xs <*> local (bindLetEnv x (typeOf xs)) (flatten e)
flatten (N.MkTuple _ es)     = P.tuple <$> mapM flatten es <*> pure Zero
flatten (N.Iterator _ h x xs)    = do
    -- Prepare an environment in which the current generator is the
    -- context
    outerScope <- ask
    let initCtx    = (x, typeOf xs)
        initTopEnv = TopEnv { topInScope = initCtx :| outerScope, topCtx = initCtx }
    
    -- In this environment, transform the iterator head
    let flatHead = runFlat initTopEnv (topFlatten h)

    P.let_ x <$> flatten xs <*> (liftLetEnv initCtx flatHead <$> ask)

-- | Lift all names bound in the environment: the value is replicated
-- for each element of the current context. The chain of 'let's is
-- terminated by the flattened head expresion of the current iterator.
liftLetEnv :: (Ident, Type) -> F.LExpr -> [(Ident, Type)] -> F.LExpr
liftLetEnv ctx headExpr env = mkLiftingLet env
  where
    mkLiftingLet :: [(Ident, Type)] -> F.LExpr
    mkLiftingLet (e : []) =
        P.let_ (fst e) (P.dist (envVar e) cv) headExpr
    mkLiftingLet (e : es) =
        P.let_ (fst e) (P.dist (envVar e) cv) (mkLiftingLet es)
    mkLiftingLet []       = headExpr

    cv :: F.LExpr
    cv = envVar ctx

--------------------------------------------------------------------------------

data TopEnv = TopEnv
    { topInScope :: NonEmpty (Ident, Type)
    , topCtx     :: (Ident, Type)
    }

bindTopEnv :: Ident -> Type -> TopEnv -> TopEnv
bindTopEnv n t e = e { topInScope = (n, t) <| topInScope e }

-- | Compile expressions nested in the top-most comprehension (with
-- iteration depth 1).
topFlatten :: N.Expr -> Flatten TopEnv F.LExpr
topFlatten (N.Table t n cs hs)  = P.dist (F.Table t n cs hs) <$> ctxVarM topCtx
topFlatten (N.UnOp t op e1)     = P.un t op <$> topFlatten e1 <*> pure (Succ Zero)
topFlatten (N.BinOp t op e1 e2) = P.bin t op <$> topFlatten e1 <*> topFlatten e2 <*> pure (Succ Zero)
topFlatten (N.Const t v)        = P.dist (F.Const t v) <$> ctxVarM topCtx
topFlatten (N.Var t v)          = return $ F.Var (liftType t) v
topFlatten (N.Let _ x xs e)     = P.let_ x <$> topFlatten xs 
                                           <*> local (bindTopEnv x (typeOf xs)) (topFlatten e)
topFlatten (N.MkTuple _ es)     = P.tuple <$> mapM topFlatten es <*> pure (Succ Zero)
topFlatten (N.If _ ce te ee)    = do

    -- Compile the boolean vector of conditions for all iterations.
    bs <- topFlatten ce

    let notL xs = P.un boolT (SUBoolOp Not) xs (Succ Zero) 

    (ctxName, ctxTy) <- asks topCtx
    let ctxVar = envVar (ctxName, ctxTy)
  
    -- For the THEN branch, consider only those iterations in which
    -- the condition is TRUE.
    -- FIXME restrict all environment entries!
    ts <- P.let_ ctxName (P.restrict ctxVar bs Zero) <$> topFlatten te

    -- For the ELSE branch, consider only those iterations in which
    -- the condition is FALSE.
    -- FIXME restrict all environment entries!
    fs <- P.let_ ctxName (P.restrict ctxVar (notL bs) Zero) <$> topFlatten ee

    -- Combine the results for the then and else branches. Combined,
    -- we get values for all iterations.
    return $ P.combine bs ts fs Zero

topFlatten (N.AppE1 _ p e)      = prim1 p <$> topFlatten e <*> pure (Succ Zero)
topFlatten (N.AppE2 _ p e1 e2)  = prim2 p <$> topFlatten e1 <*> topFlatten e2 <*> pure (Succ Zero)
topFlatten (N.Iterator _ h x xs) = do
    -- The compiled generator expression of the current iterator,
    -- compiled in the context of the topmost comprehension.
    currentGen <- topFlatten xs

    -- The current context, i.e. the context generated by the
    -- outermost iterator.
    outerScope <- asks topInScope

    -- The new context spanned by the current generator
    let innerCtx = (x, typeOf currentGen)

    -- Initialize the environment for descending into the
    -- comprehension head
    let nestedEnv = initEnv innerCtx outerScope

    let flatHead = runFlat nestedEnv (deepFlatten h)

    -- Bind the generator of the current iterator, then lift the
    -- environment and terminate with the flattened head of the
    -- current iterator.
    P.let_ x currentGen <$> (liftTopEnv innerCtx flatHead <$> asks topInScope)

-- | Lift all names bound in the environment: the value is replicated
-- for each element of the current context. The chain of 'let's is
-- terminated by the flattened head expression of the current
-- iterator.
liftTopEnv :: (Ident, Type) -> F.LExpr -> NonEmpty (Ident, Type) -> F.LExpr
liftTopEnv ctx headExpr env = mkLiftingLet env
  where
    mkLiftingLet :: NonEmpty (Ident, Type) -> F.LExpr
    mkLiftingLet (e :| [])  =
        P.let_ (fst e) (P.distL (envVar e) cv) headExpr
    mkLiftingLet (e :| (e2 : es)) =
        P.let_ (fst e) (P.distL (envVar e) cv) (mkLiftingLet (e2 :| es))

    cv :: F.LExpr
    cv = envVar ctx

--------------------------------------------------------------------------------
-- Compile expressions which are nested deeper, i.e. at least at
-- iteration depth 2.

-- | The environment stores all information for dealing with deeper
-- nested expressions.
-- FIXME env should be NonEmpty
data NestedEnv = NestedEnv

    { -- | A reference to the generator expression in the current
      -- iteration context.
      context    :: (Ident, Type)   

      -- | All bindings which are currently in scope and need to be
      -- lifted to the current iteration context.
    , inScope    :: NonEmpty (Ident, Type) 

      -- | The current iteration depth
    , frameDepth :: Nat
    }

-- | 'initEnv x xst ctx' constructs the initial environment when a
-- comprehension is encountered at depth 1. 'x' is the variable bound
-- by the inner comprehension, 'xst' is the type of the /translated/
-- generator source expression and 'ctx' is the outer (so far)
-- context.
initEnv :: (Ident, Type) -> NonEmpty (Ident, Type) -> NestedEnv
initEnv (x, xst) outerScope = 
    NestedEnv { context    = (x, xst)
              , inScope    = fmap (\(n, t) -> (n, liftType t)) 
                                  ((x, xst) <| outerScope)
              , frameDepth = Succ $ Succ Zero
              }

bindNestedEnv :: Ident -> Type -> NestedEnv -> NestedEnv
bindNestedEnv n t e = e { inScope = (n, t) <| inScope e }

-- | A reader monad that provides access to the flattening
-- environment.
type DeepFlatten a = Reader NestedEnv a


-- | Update the environment to express the descent into a
-- comprehension that binds the name 'x'. This involves updating the
-- context, binding 'x' in the current environment frame and
-- increasing the frame depth.
descendEnv :: (Ident, Type) -> NestedEnv -> NestedEnv
descendEnv x env = env { context    = x
                       , inScope    = x <| inScope env 
                       , frameDepth = Succ $ frameDepth env
                       }

frameDepthM :: DeepFlatten Nat
frameDepthM = asks frameDepth

-- Compile nested expressions that occur with an iteration depth of at
-- least two.
deepFlatten :: N.Expr -> Flatten NestedEnv F.LExpr
deepFlatten (N.Var t v)          = frameDepthM >>= \d -> return $ F.Var (liftTypeN d t) v
-- FIXME abstract over dist
deepFlatten (N.Table t n cs hs)  = do
    Succ d1 <- frameDepthM
    ctx     <- ctxVarM context
    return $ P.imprint d1 ctx $ P.dist (F.Table t n cs hs) (P.forget d1 ctx)

-- FIXME abstract over dist
deepFlatten (N.Const t v)        = do
    Succ d1 <- frameDepthM
    ctx     <- ctxVarM context
    return $ P.imprint d1 ctx $ P.dist (F.Const t v) (P.forget d1 ctx)

deepFlatten (N.UnOp t op e1)     = P.un t op <$> deepFlatten e1 <*> frameDepthM
deepFlatten (N.BinOp t op e1 e2) = P.bin t op <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM
deepFlatten (N.MkTuple _ es)     = frameDepthM >>= \d -> P.tuple <$> mapM deepFlatten es <*> pure d
deepFlatten (N.AppE1 _ p e)      = prim1 p <$> deepFlatten e <*> frameDepthM
deepFlatten (N.AppE2 _ p e1 e2)  = prim2 p <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM

deepFlatten (N.Let _ x xs e)     = P.let_ x <$> deepFlatten xs 
                                            <*> local (bindNestedEnv x (typeOf xs)) (deepFlatten e)

-- FIXME abstract over environment restriction wrt. to depth
deepFlatten (N.If _ ce te ee)    = do
    Succ d1      <- frameDepthM
    
    -- Lift the condition
    bs           <- deepFlatten ce
    
    -- Lift the THEN branch. Note that although the environment record
    -- does not change, all environment variables are re-bound to a
    -- restricted environment by 'restrictEnv'.
    thenExpr     <- deepFlatten te

    -- Lift the ELSE branch. See comment above.
    elseExpr     <- deepFlatten ee

    env          <- asks inScope

    -- Construct the restricted environments in which the THEN and
    -- ELSE branches are evaluated.
    let notL xs = P.un boolT (SUBoolOp Not) xs (Succ d1) 
    
        thenRes = restrictEnv env d1 bs thenExpr

        elseRes = restrictEnv env d1 (notL bs) elseExpr

    return $ P.combine bs thenRes elseRes d1

-- FIXME lift types in the environment (add one list type constructor)
deepFlatten (N.Iterator _ h x xs)    = do
    d@(Succ d1) <- frameDepthM
    env         <- asks inScope
    let cv' = (x, liftTypeN (Succ d) (typeOf xs))
    headExpr    <- local (descendEnv cv') $ deepFlatten h

    xs'         <- deepFlatten xs

    return $ P.let_ x xs' (liftNestedEnv cv' d1 headExpr env)

restrictEnv :: NonEmpty (Ident, Type) -> Nat -> F.LExpr -> F.LExpr -> F.LExpr
restrictEnv env d1 bs branchExpr = mkRestrictLet env
  where
    mkRestrictLet :: NonEmpty (Ident, Type) -> F.LExpr
    mkRestrictLet (e :| []) =
        P.let_ (fst e)
               (P.restrict (envVar e) bs d1)
               branchExpr
    mkRestrictLet (e :| (e2 : es)) = 
        P.let_ (fst e)
               (P.restrict (envVar e) bs d1)
               (mkRestrictLet (e2 :| es))

-- | Lift all names bound in the environment: the value is replicated
-- for each element of the current context. The chain of 'let's is
-- terminated by the flattened head expression of the current
-- iterator.
liftNestedEnv :: (Ident, Type) -> Nat -> F.LExpr -> NonEmpty (Ident, Type) -> F.LExpr
liftNestedEnv ctx d1 headExpr env = mkLiftingLet env
  where
    mkLiftingLet :: NonEmpty (Ident, Type) -> F.LExpr
    mkLiftingLet (e :| [])  =
        P.let_ (fst e) 
               (P.imprint d1 cv (P.distL (P.forget d1 $ envVar e) (P.forget d1 cv)))
               headExpr
    mkLiftingLet (e :| (e2 : es)) =
        P.let_ (fst e) 
               (P.imprint d1 cv (P.distL (P.forget d1 $ envVar e) (P.forget d1 cv)))
               (mkLiftingLet (e2 :| es))

    cv :: F.LExpr
    cv = envVar ctx

--------------------------------------------------------------------------------
-- Normalization of intermediate flat expressions into the final
-- form. This step eliminates higher-lifted occurences of built-in
-- combinators.

type Supply = Int

type NormFlat a = State Supply a

freshNameN :: NormFlat Ident
freshNameN = do
    i <- get
    put $ i + 1
    return $ "nf" ++ show i

normalize :: F.LExpr -> F.FExpr
normalize e = evalState (normLifting e) 0

-- | Reduce all higher-lifted occurences of primitive combinators and
-- operators to singly lifted variants by flattening the arguments and
-- restoring the original list shape on the result.
normLifting :: F.LExpr -> NormFlat F.FExpr
normLifting (F.Table t n cs hs)    = return $ F.Table t n cs hs
normLifting (F.If t ce te ee)      = F.If t <$> normLifting ce <*> normLifting te <*> normLifting ee
normLifting (F.Const t v)          = return $ F.Const t v
normLifting (F.Var t n)            = return $ F.Var t n
normLifting (F.Forget n t e)       = F.Forget n t <$> normLifting e
normLifting (F.Imprint n t e1 e2)  = F.Imprint n t <$> normLifting e1 <*> normLifting e2
normLifting (F.Let t x e1 e2)      = F.Let t x <$> normLifting e1 <*> normLifting e2
normLifting (F.MkTuple t l es)     =
    case l of
        F.LiftedN Zero         -> F.MkTuple t F.NotLifted <$> mapM normLifting es
        F.LiftedN (Succ Zero)  -> F.MkTuple t F.Lifted <$> mapM normLifting es
        F.LiftedN (Succ d)     -> do
            e1' : es' <- mapM normLifting es
            n         <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.MkTuple (unliftTypeN d t) F.Lifted (P.forget d v : map (P.forget d) es')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.UnOp t op l e)      = 
    case l of
        F.LiftedN Zero         -> F.UnOp t op F.NotLifted <$> normLifting e
        F.LiftedN (Succ Zero)  -> F.UnOp t op F.Lifted <$> normLifting e
        F.LiftedN (Succ d)     -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.UnOp (unliftTypeN d t) op F.Lifted (P.forget d v)
            return $ P.let_ n e' $ P.imprint d v app

normLifting (F.BinOp t op l e1 e2)  = 
    case l of
        F.LiftedN Zero         -> F.BinOp t op F.NotLifted
                                            <$> normLifting e1
                                            <*> normLifting e2
        F.LiftedN (Succ Zero)  -> F.BinOp t op F.Lifted
                                            <$> normLifting e1
                                            <*> normLifting e2
        F.LiftedN (Succ d)     -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.BinOp (unliftTypeN d t) op F.Lifted (P.forget d v) (P.forget d e2')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.PApp1 t p l e)    = 
    case l of
        F.LiftedN Zero         -> F.PApp1 t p F.NotLifted <$> normLifting e
        F.LiftedN (Succ Zero)  -> F.PApp1 t p F.Lifted <$> normLifting e
        F.LiftedN (Succ d)     -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.PApp1 (unliftTypeN d t) p F.Lifted (P.forget d v)
            return $ P.let_ n e' (P.imprint d v app)

normLifting (F.PApp2 t p l e1 e2)   = 
    case l of
        F.LiftedN Zero         -> F.PApp2 t p F.NotLifted
                                              <$> normLifting e1
                                              <*> normLifting e2
        F.LiftedN (Succ Zero)  -> F.PApp2 t p F.Lifted
                                              <$> normLifting e1
                                              <*> normLifting e2
        F.LiftedN (Succ d)     -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp2 (unliftTypeN d t) p F.Lifted (P.forget d v) (P.forget d e2')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.PApp3 t p l e1 e2 e3)    = 
    case l of
        F.LiftedN Zero        -> F.PApp3 t p F.NotLifted
                                             <$> normLifting e1
                                             <*> normLifting e2
                                             <*> normLifting e3
        F.LiftedN (Succ Zero) -> F.PApp3 t p F.Lifted
                                             <$> normLifting e1
                                             <*> normLifting e2
                                             <*> normLifting e3
        F.LiftedN (Succ d)    -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            e3' <- normLifting e3
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp3 (unliftTypeN d t) p F.Lifted (P.forget d v) 
                                                           (P.forget d e2') 
                                                           (P.forget d e3')
            return $ P.let_ n e1' $ P.imprint d v app
