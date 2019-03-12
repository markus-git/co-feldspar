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

import Prelude hiding ((/=), length, div)

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

fftCore
  :: forall vec a .
     ( Manifestable Software vec (SExp (Complex a))
     , Finite SExp vec
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     , Indexed SExp vec 
     , ArrElem vec ~ SExp (Complex a)
     )
  => Store Software (SExp (Complex a))
  -> Bool        -- ^ Inverese?
  -> SExp Length -- ^ Iteration count
  -> vec         -- ^ Initial vector
  -> Software (Manifest Software (SExp (Complex a)))
fftCore st inverse n vec =
    loopStore st (n+1) (-1) (1) (\ix -> return . ilv2 ix) vec
  where
    ilv2 :: SExp Index -> Manifest Software (SExp (Complex a)) ->
      Push Software (SExp (Complex a))
    ilv2 k vec = Push len $ \write ->
        dumpPush (toPush vec2) $ \i (a, b) -> do
          write (left  i) a
          write (right i) b
      where
        len  = length vec  :: SExp Index
        len2 = len `div` 2 :: SExp Index
        ix   = i2n k       :: SExp Int32
        ix2  = 1 .<<. ix   :: SExp Index
        left  = zeroBit k
        right = flipBit k . left
        vec2  = Pull len2 ixf
        ixf j = (a+b, twid * (a-b))
          where
            a    = vec ! (left  j)
            b    = vec ! (right j)
            pi'  = if inverse then pi else -pi
            twid = polar 1 (pi' * i2n (leastBits ix (right j)) / i2n ix2)

fftContainer
  :: ( Manifestable Software vec (SExp (Complex a))
     , Finite SExp vec
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     , Indexed SExp vec 
     , ArrElem vec ~ SExp (Complex a)
     )
  => Store Software (SExp (Complex a))
  -> Bool
  -> vec
  -> Software (Manifest Software (SExp (Complex a)))
fftContainer st inverse vec = do
  n <- shareM (ilog2 (length vec) - 1)
  v <- fftCore st inverse n vec
  st <- replaceFreeStore (length v) st
  revBit st n v

fft
  :: ( Manifestable Software vec (SExp (Complex a))
     , Finite SExp vec
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     , Indexed SExp vec 
     , ArrElem vec ~ SExp (Complex a)
     )
  => Store Software (SExp (Complex a))
  -> vec
  -> Software (Manifest Software (SExp (Complex a)))
fft st = fftContainer st False


--------------------------------------------------------------------------------

testFFT :: Software ()
testFFT = do
  st  :: Store Software (SExp (Complex Float)) <- newStore 5
  arr :: Array Software (SExp (Complex Float)) <- initArr [0.2,0.1,0.2,0.1,0.2]
  brr <- unsafeFreezeArr arr
  fft st brr
  return ()

--------------------------------------------------------------------------------

rotBit :: SExp Index -> SExp Index -> SExp Index
rotBit k i = lefts .|. rights
  where
    k' = i2n k
    ir = i .>>. 1
    rights = ir .&. oneBits k'
    lefts  = (((ir .>>. k') .<<. 1) .|. (i .&. 1)) .<<. k'

riffle :: (Pully SExp vec a, Syntax SExp a) => SExp Index -> vec -> Pull SExp a
riffle = backPermute . const . rotBit

revBit :: (Manifestable Software vec a, Finite SExp vec, SyntaxM Software a)
  => Store Software a -> SExp Length -> vec -> Software (Manifest Software a)
revBit st n = loopStore st 1 1 n $ \i -> return . riffle i

--------------------------------------------------------------------------------

oneBits :: (Bits a, Num a, SType a, SoftwarePrimType a) =>
  SExp Int32 -> SExp a
oneBits n = complement (ones .<<. n)

testBit :: (Bits a, Num a, SType a, SoftwarePrimType a) =>
  SExp a -> SExp Index -> SExp Bool
testBit a i = a .&. (1 .<<. i2n i) /= 0

flipBit :: (Bits a, Num a, SType a, SoftwarePrimType a) =>
  SExp Index -> SExp a -> SExp a
flipBit i a = a `xor` (1 .<<. (i2n i))

zeroBit :: (Bits a, Num a, SType a, SoftwarePrimType a) =>
  SExp Index -> SExp a -> SExp a
zeroBit i a = a + (a .&. (ones .<<. (i2n i)))

leastBits :: (Bits a, Num a, SType a, SoftwarePrimType a) =>
  SExp Int32 -> SExp a -> SExp a
leastBits i a = a .&. oneBits i

--------------------------------------------------------------------------------
