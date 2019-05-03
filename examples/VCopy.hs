{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module VCopy where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Array.Buffered

import Feldspar.Software
import Feldspar.Software.Verify
import Feldspar.Software as Soft (icompile)

--import Feldspar.Hardware
--import Feldspar.Hardware as Hard (icompile)

import Prelude hiding (take, drop, reverse, length, map, zip, zipWith, sum, div)

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

reverse' :: SType a => Manifest Software (SExp a) -> SPush (SExp a)
reverse' (M iarr) = Push len $ \write -> do
    arr <- unsafeThawArr iarr
    for 0 1 (len `div` 2) $ \ix -> do
      a <- getArr arr (len-ix-1)
      b <- getArr arr (ix)
      write (ix)       a
      write (len-ix-1) b
  where
    len = length iarr

prog :: Software ()
prog = do
  buf :: Store Software (SExp Word32) <- newStore 20
  vec1 <- store buf $ (1...20)
  vec2 <- store buf $ reverse' vec1
  printf "%d" $ sum $ map (*2) vec2

prog' :: Software ()
prog' = do
  buf :: Store Software (SExp Word32) <- newInPlaceStore 20
  vec1 <- store buf $ (1...20)
  vec2 <- store buf $ reverse' vec1
  printf "%d" $ sum $ map (*2) vec2


--------------------------------------------------------------------------------
