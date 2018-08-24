{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Processing where

import Feldspar
import Feldspar.Software

import Feldspar.Array.Vector
import Feldspar.Array.Queue

import Prelude hiding (sum, zipWith, length, replicate, tail, reverse, inits, map)

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

dot :: SPull (SExp Int16) -> SPull (SExp Int16) -> SExp Int16
dot xs ys = sum (zipWith (*) xs ys)

fir :: SPull (SExp Int16) -> SPull (SExp Int16) -> Seq Software (SExp Int16)
fir as bs = recurrenceI (replicate (length as) 0) bs $ \i -> dot as i

--------------------------------------------------------------------------------

-- FIR filter without the queue, its second input should be manifested.
firQ :: SPull (SExp Int16) -> SPull (SExp Int16) -> SPull (SExp Int16)
firQ as bs = map (dot as . reverse) $ tail $ inits bs

--------------------------------------------------------------------------------

test :: Software ()
test =
  do as :: Arr (SExp Int16) <- initArr [1, 2, 3, 4 :: Int16]
     bs :: Arr (SExp Int16) <- initArr [4, 3, 2, 1 :: Int16]
     --
     ias <- unsafeFreezeArr as
     ibs <- unsafeFreezeArr bs
     --
     res <- manifestFresh $ firQ (toPull ias) (toPull ibs)
     --
     cs  <- thawArr $ manifest res
     --
     return ()

--------------------------------------------------------------------------------
