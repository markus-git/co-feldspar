{-# language TypeFamilies        #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Tut5_Memory where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Array.Buffered
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

import Control.Monad (void)

import Prelude hiding (map, zipWith, sum, take, reverse, (++))

--------------------------------------------------------------------------------
-- * Memory manegement.
--------------------------------------------------------------------------------

-- todo: write text.
genericPushy
  :: (Pully (Expr m) vec a, Num a, SyntaxM m a, VectorM m, MonadComp m, Loop m)
  => vec -> Push m a
genericPushy vec = reverse vec ++ map (*2) vec

-- A previous example showed the use of `manifestFresh` to store the content of
-- a vector in memory and get a manifest vector back as result. The problem with
-- this function is that it allocates an array under the hood. Often times,
-- vector operations are done in a "pipeline" consisting of many stages. In such
-- cases, one typically wants to allocate a small number of arrays and use
-- throughout the pipeline.
buildPushy_safe :: forall m .
     ( SyntaxM m (Expr m Word32)
     , VectorM m
     , MonadComp m
     , Loop m
     --
     , Finite   (Expr m) (Array  m (Expr m Word32))
     , Slicable (Expr m) (IArray m (Expr m Word32))
     --
     , Pully (Expr m) (IArray m (Expr m Word32)) (Expr m Word32)
     -- 
     , Num  (Internal (Expr m Length))
     , Enum (Internal (Expr m Length))
     )
  => Expr m Word32
  -> m (Manifest m (Expr m Word32))
buildPushy_safe n =
  do vec <- listManifest [n]
     vec <- manifestFresh (genericPushy vec :: Push m (Expr m Word32))
     vec <- manifestFresh (genericPushy vec :: Push m (Expr m Word32))
     vec <- manifestFresh (genericPushy vec :: Push m (Expr m Word32))
     vec <- manifestFresh (genericPushy vec :: Push m (Expr m Word32))
     vec <- manifestFresh (genericPushy vec :: Push m (Expr m Word32))
     return vec
-- Note that, although this function is completely safe, allocating a fresh
-- array for each intermediate vector puts high pressure on the stack.

buildPushy_safeProg :: Software ()
buildPushy_safeProg =
  do void $ buildPushy_safe 10

test1 = Soft.icompile buildPushy_safeProg


--------------------------------------------------------------------------------

-- Another alternative is to allocate *one* storage, and use the function
-- `store` to store the intermediate vectors:
buildPushy_managed
  :: forall m .
     ( SyntaxM m (Expr m Word32)
     , VectorM m
     , MonadComp m
     , Loop m
     --
     , Finite   (Expr m) (Array  m (Expr m Word32))
     , Slicable (Expr m) (IArray m (Expr m Word32))
     --
     , Pully (Expr m) (IArray m (Expr m Word32)) (Expr m Word32)
     --
     , Num  (Internal (Expr m Word32))
     , Enum (Internal (Expr m Word32))
     --
     , ArraysSwap m
     , ArraysEq (Array m) (IArray m)
     )
  => Expr m Word32 -> m (Manifest m (Expr m Word32))
buildPushy_managed n =
  do st  <- newStore 32
     vec <- store st (listPush [n] :: Push m (Expr m Word32))
     vec <- store st (genericPushy vec :: Push m (Expr m Word32))
     vec <- store st (genericPushy vec :: Push m (Expr m Word32))
     vec <- store st (genericPushy vec :: Push m (Expr m Word32))
     vec <- store st (genericPushy vec :: Push m (Expr m Word32))
     vec <- store st (genericPushy vec :: Push m (Expr m Word32))
     return vec

--------------------------------------------------------------------------------
