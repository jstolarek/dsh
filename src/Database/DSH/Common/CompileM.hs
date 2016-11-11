module Database.DSH.Common.CompileM
    ( Compile, runCompile, runLineage, freshVar
    ) where

import           Control.Monad.State

-- In the state, we store a counter for fresh variable names.
type CompileState = Integer

-- | The Compile monad provides fresh variable names.
type Compile = State CompileState

-- | Provide a fresh identifier name during compilation
freshVar :: Compile Integer
freshVar = do
    i <- get
    put $ i + 1
    return i

-- | Run compilation computation.
runCompile :: Compile a -> a
runCompile ma = evalState ma 0 -- see Note [Unique names hack]

-- | Run lineage transformation
runLineage :: Compile a -> a
runLineage ma = evalState ma 1000 -- see Note [Unique names hack]

-- Note [Unique names hack]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- It is essential that variable names created during lineage transform and
-- compilation from FL to CL are distinct.  To achieve this we usa a ugly hack:
-- variables generated during compilation are numbered from 0, and those
-- generated during lineage transformation are numbered from 1000.  If
-- compilation of lineage-transformed query ever generates more than 1000
-- variables things will break.
