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
-- * Basic example of arrays in co-feldspar.
--------------------------------------------------------------------------------

arrays
  :: forall m dom expr
   . ( Comp m
     , dom  ~ DomainOf m
     , expr ~ Expr m

     -- *** todo: ...
     , Num (Ix m)
     , Elem (IArray m (expr Int8)) ~ expr Int8
     , Finite (Ix m) (Array m (expr Int8))

     -- *** todo: ...
     , Indexed dom (expr Index) (IArray m (expr Int8))

     , Num (expr Int8)
     , Syntax dom (expr Int8)
     )
  => m ()
arrays =
  do arr :: Array m (expr Int8) <- newArr 2
     setArr arr 0 0
     setArr arr 1 1

     v <- getArr arr 1
     ref :: Reference m (expr Int8) <- initRef v

     iarr :: IArray m (expr Int8) <- freezeArr arr
     setArr arr 1 2
     setRef ref (iarr ! (1 :: expr Index))
     
--------------------------------------------------------------------------------
