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
   . ( Comp m
     , dom  ~ Dom  m -- for instances below, should be hidden.
     , expr ~ Expr m -- we don't have SExp/HExp yet.
     
     , Equality dom, Ordered dom, Logical dom
         -- todo : that we need to show `dom` ^ is unfortunate.
     , Num (expr Int8)
         -- todo : Syntax' ... a, Num (Internal a) => Num a.
     , Syntax dom (expr Int8)
     , Syntax dom (expr Int8, expr Int8)
         -- todo : removing ^ gives a wierd error message, I should have
         -- specific instances for primitive values and that => pairs.
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
