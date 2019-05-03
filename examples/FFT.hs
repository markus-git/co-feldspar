{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language FlexibleContexts #-}


module FFT where

import Feldspar
import Feldspar.Software hiding (Arr)
import Feldspar.Software.Verify
import Feldspar.Array.Vector
import Feldspar.Array.Buffered

import Data.Bits (Bits)
import Data.Complex (Complex)

import Prelude hiding ((/=), length)

--------------------------------------------------------------------------------
-- * FFT
--------------------------------------------------------------------------------

type SStore  a = Store  Software a
type SSyntax a = Syntax SExp a

-- | Collection of constraints for immutable arrays.
type Immutable arr a = (
    Manifestable Software arr a
  , Finite   SExp arr
  , Indexed  SExp arr, ArrElem arr ~ a
  , Slicable SExp arr
  )

--------------------------------------------------------------------------------
-- ** Helper functions.

-- | Creates a value of type @a@ where the lowest @n@ bits are ones.
oneBits :: (Bits a, Num (SExp a), SType' a)
  => SExp Int32 -> SExp a
oneBits n = complement (ones .<<. n)

-- | Check if the @i@'th bit of @a@ is a one.
testBit :: (Integral a, Bits a, Num (SExp a), SType' a) =>
  SExp a -> SExp Index -> SExp Bool
testBit a i = i2b (a .&. (1 .<<. i2n i))

-- | Flip the @i@'th bit of @a@.
flipBit :: (Bits a, Num (SExp a), SType' a) =>
  SExp Index -> SExp a -> SExp a
flipBit i a = a `xor` (1 .<<. (i2n i))

-- | 
zeroBit :: (Bits a, Num (SExp a), SType' a) =>
  SExp Index -> SExp a -> SExp a
zeroBit i a = a + (a .&. (ones .<<. (i2n i)))

-- | Zeroes all but the lowest @i@ bits in @a@.
leastBits :: (Bits a, Num (SExp a), SType' a) =>
  SExp Int32 -> SExp a -> SExp a
leastBits i a = a .&. oneBits i

-- | Two to the power of @n@, i.e. @2^n@.
pow2 :: (Num (SExp a), Bits a, SType' a)
  => SExp Index -> SExp a
pow2 n = 1 .<<. i2n n

--------------------------------------------------------------------------------
-- ** Riffle network.

-- | Riffle indices.
rotBit :: SExp Index -> SExp Index -> SExp Index
rotBit k i = lefts .|. rights
  where
    k'     = i2n k
    ir     = i .>>. 1
    rights = ir .&. oneBits k'
    lefts  = (((ir .>>. k') .<<. 1) .|. (i .&. 1)) .<<. k'

-- | Riffle network for a pully array.
riffle :: (Immutable arr a, SSyntax a)
  => SExp Index -> arr -> SPull a
riffle k arr = Pull (length arr) $ \i -> arr ! rotBit k i

-- | 
revBit :: (Immutable arr a, SSyntax a)
  => SStore a -> SExp Length -> arr -> Software (SManifest a)
revBit st n vec = loopStore st 1 1 (n-1) (step) vec
  where
    step i arr = return $ riffle i arr

--------------------------------------------------------------------------------
-- ** Twiddle factors.

-- | 
tw :: (Floating a, SType' a, SType' (Complex a))
  => SExp Index -> SExp Index -> SExp (Complex a)
tw n k = polar 1 (-2 * pi * i2n k / i2n n)

-- | 
twids
  :: ( Immutable ts  (SExp (Complex a))
     , Immutable vec (SExp (Complex a))
     , SType' a
     , SType' (Complex a)
     , RealFloat a
     )
  => ts
  -> SExp Index
  -> SExp Index
  -> SExp Length
  -> vec
  -> SPull (SExp (Complex a))
twids ts n k l vec = Pull l $ \i ->
  let
    j = (leastBits (i2n k) i) .<<. (n'-1-k')
  in
    (testBit i k) ? ((ts!j) * (vec!i)) $ (vec!i)
  where
    n' = i2n n
    k' = i2n k

--------------------------------------------------------------------------------
-- ** Butterfly.

-- | Butterfly network.
bfly
  :: ( Immutable vec (SExp (Complex a))
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     )
  => SExp Index -> vec -> SPull (SExp (Complex a))
bfly k as = Pull (length as) $ \i ->
    let a = as ! i
        b = as ! flipBit i k
    in  (testBit i k) ? (b-a) $ (a+b)

--------------------------------------------------------------------------------
-- ** FFT Core.

-- | Core of the FFT
fftCore
  :: ( Immutable ts  (SExp (Complex a))
     , Immutable vec (SExp (Complex a))
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     )
  => SStore (SExp (Complex a))
  -> ts
  -> SExp Length
  -> vec
  -> Software (SManifest (SExp (Complex a)))
fftCore st ts n vec =
  let
    step i = return . twids ts n i (length vec) . bfly i
  in
    do arr <- loopStore st ((i2n n)-1) (-1) 0 (step . i2n) vec
       revBit st n arr

-- | Radix-2 Decimation-In-Frequency Fast Fourier Transformation of the given
-- complex vector. The given vector must be power-of-two sized, (for example 2,
-- 4, 8, 16, 32, etc.) The output is non-normalized.
fft
  :: ( Immutable vec (SExp (Complex a))
     , RealFloat a
     , SType' a
     , SType' (Complex a)
     )
  => SStore (SExp (Complex a))
  -> vec
  -> Software (SManifest (SExp (Complex a)))
fft st vec =
  do n  <- shareM (ilog2 (length vec))
     ts <- manifestFresh $ Pull (pow2 (n-1)) (tw (pow2 n))
     fftCore st ts n vec

--------------------------------------------------------------------------------
