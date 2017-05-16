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

       -- ^ Supported co-feldspar expressoins.
       -- 
       -- todo: that we need to show `dom` is unfortunate but it is possible
       -- to hide 'type EqualityM m = Equality (DomainOf m)', I just need to
       -- find a prettier way of hiding `dom`.
     , Equality dom, Ordered dom, Logical dom

       -- ^ Supported Haskell expressions.
       --
       -- todo: Syntax(') m a, Num (Internal a) => Num a.
     , Num (expr Int8)

       -- ^ Our expressions are of a know kind co-feldspar and correctly typed.
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
-- * Type casting.
--------------------------------------------------------------------------------

casting
  :: forall m
   . ( Comp m
     , SyntaxM m (Expr m Word8)
     , SyntaxM m (Expr m Word32)
     , Num (Expr m Word8)
     , Num (Expr m Word32)

     , Casting (DomainOf m)
     
     -- I should probably get rid of these.
     , PredicateOf (DomainOf m) Word8
     , PredicateOf (DomainOf m) Word32
     , Internal (Expr m Word8)  ~ Word8
     , Internal (Expr m Word32) ~ Word32
     )
  => m ()
casting =
  do a :: Reference m (Expr m Word8)  <- initRef 200
     b :: Reference m (Expr m Word32) <- initRef 500

     va <- getRef a
     vb <- getRef b

     setRef a (i2n vb)
     setRef b (i2n va)

-- example compiles with:
--   - Soft.icompile example
--   - Hard.icompile example
--
--------------------------------------------------------------------------------
