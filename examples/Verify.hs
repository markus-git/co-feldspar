{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language ScopedTypeVariables #-}

module Verify where

import Feldspar
import Feldspar.Software
import Feldspar.Software.Verify
import Feldspar.Array.Vector
import Feldspar.Array.Buffered

import Data.Bits (Bits)
import Data.Complex (Complex)

import Prelude hiding ((==), (/=), length, div)

--------------------------------------------------------------------------------

-- A super-simple verification example.
count :: Software ()
count = do
  printf "Enter a number: "
  n :: SExp Word32 <- fget stdin

  let total = iter n 0 (\i n -> hintVal (n == i) $ i + 1)
  total <- initRef total >>= unsafeFreezeRef
  assert (total == n) "Count is wrong"
  printf "The count is %d\n" total

------------------------------------------------------------
{-
test_scProd1 = do
    n <- fget stdin
    printf "result: %.3f\n" $
      (scProd (fmap i2n (0 ... n-1)) (fmap i2n (2 ... n+1)) :: Data Double)

test_scProd2 = do
    n  <- fget stdin
    v1 <- manifestFresh $ fmap i2n (0 ... n-1)
    v2 <- manifestFresh $ fmap i2n (2 ... n+1)
    printf "result: %.3f\n" (scProd v1 v2 :: Data Double)

map_inplace :: Run ()
map_inplace = do
    n   <- fget stdin
    loc <- newArr n
    vec <- manifest loc (0 ... n-1)
    manifestStore loc $ map (+1) vec
    vec <- unsafeFreezeArr loc
    printf "result: %d\n" $ sum vec

map2_inplace :: Run ()
map2_inplace = do
    n   <- fget stdin
    assert (n < maxBound) "oops"
    loc :: Arr (Data Word32) <- newArr (n+1)
    vec <- unsafeFreezeArr loc
    for (0, 1, Excl (n :: Data Word32)) $ \i -> do
      setArr loc i (arrIx vec i+1)

tail_inplace :: Run ()
tail_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc
    let when cond x = iff cond x (return ())
    when (n > 0) $
      for (0, 1, Excl (n-1)) $ \i -> do
        setArr loc i (arrIx vec (i+1)+1)

filter_inplace :: Run ()
filter_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc
    ref <- initRef 0
    let when cond x = iff cond x (return ())
    for (0, 1, Excl n) $ \i -> do
      let x = arrIx vec i
      when (x > 5) $ do
        j <- unsafeFreezeRef ref
        hint (j <= i)
        setArr loc j x
        setRef ref (j+1)

rev_inplace :: Software ()
rev_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc >>= unsafeThawArr
    for (0, 1, Excl (n `div` 2 :: Data Word32)) $ \i -> do
      x <- getArr vec i
      y <- getArr vec (n-i-1)
      setArr loc i y
      setArr loc (n-i-1) x
-}
--------------------------------------------------------------------------------
