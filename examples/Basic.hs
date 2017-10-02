{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompileWrap)

--------------------------------------------------------------------------------
-- * Basic example of how our hardware software co-design works.
--------------------------------------------------------------------------------

example
  :: forall m dom expr
   . ( MonadComp m
     , Equality (Expr m)
     , Ordered  (Expr m)
     , Logical  (Expr m)
       -- ^ Supported Haskell expressions.
     , Num (Expr m Int8)
       -- ^ Our expressions are of a know kind co-feldspar and correctly typed.
     , SyntaxM m (Expr m Int8)
     , SyntaxM m (Expr m Int8, Expr m Int8)
     )
  => m ()
example =
  do r :: Reference m (Expr m Int8) <- initRef 2
     k :: Reference m (Expr m Int8, Expr m Int8) <- newRef
     a <- getRef r
     setRef k (a, a + a)

-- example compiles with:
--   - Soft.icompile example
--   - Hard.icompile example
--
--------------------------------------------------------------------------------

soft :: Software ()
soft = example

-- example compiles with:
--   - Soft.icompile soft
--
--------------------------------------------------------------------------------

hard :: Hardware ()
hard = example

-- example compiles with:
--   - Hard.icompile hard
--
--------------------------------------------------------------------------------
