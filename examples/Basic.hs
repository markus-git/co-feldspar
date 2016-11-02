{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import qualified Feldspar.Software.Compile as Soft

import Feldspar.Hardware
import qualified Feldspar.Hardware.Compile as Hard

import Language.Syntactic (Internal)

--------------------------------------------------------------------------------
-- * Basic example of how our hardware software co-design works.
--------------------------------------------------------------------------------

example
  :: forall m dom expr
   . ( Monad m, References m, dom ~ Dom m, expr ~ Expr m
       -- ^ Instructions `m` support.
     , Value dom, Share dom
       -- ^ General constructs that `m`'s expression type supports.
     , Equality dom, Ordered dom, Logical dom
       -- ^ Primitive functions that `m`'s expression type supports.
       
     , Num (expr Int8)
         -- *** todo : Num a => Num (expr a).
     , Syntax dom (expr Int8)
     , Syntax dom (expr Int8, expr Int8)
         -- *** todo : removing ^ gives a wierd error message, I should have
         --     specific instances for primitive values and => pairs.
     )
  => m ()
example =
  do r :: Reference m (expr Int8) <- initRef 2
     k :: Reference m (expr Int8, expr Int8) <- newRef

     a <- getRef r
     setRef k (a, a)

--------------------------------------------------------------------------------

soft :: Software ()
soft = example
  -- Soft.icompile bepa

--------------------------------------------------------------------------------

hard :: Hardware ()
hard = example
  -- Hard.icompile cepa

--------------------------------------------------------------------------------
