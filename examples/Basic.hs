{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile)

--------------------------------------------------------------------------------
-- * Basic example of how our hardware software co-design works.
--------------------------------------------------------------------------------

example
  :: forall m dom expr
   . ( Comp m
     , dom  ~ DomainOf m -- for instances below, should be hidden.
     , expr ~ Expr m     -- we don't have SExp/HExp yet.
     
     , Equality dom, Ordered dom, Logical dom
         -- todo : that we need to show `dom` ^ is unfortunate.
     , Num (expr Int8)
         -- todo : Syntax' ... a, Num (Internal a) => Num a.
     , Syntax dom (expr Int8)
     )
  => m ()
example =
  do r :: Reference m (expr Int8) <- initRef 2
     k :: Reference m (expr Int8, expr Int8) <- newRef
     a <- getRef r
     setRef k (a, a + a)

-- example compiles with:
--   - Soft.icompile example
--   - Hard.icompile example
--
--------------------------------------------------------------------------------

soft :: Software ()
soft = example

-- soft compiles with:
--   - Soft.icompile soft
--
--------------------------------------------------------------------------------

hard :: Hardware ()
hard = example

-- hard compiles with:
--   - Hard.icompile cepa
--
--------------------------------------------------------------------------------
