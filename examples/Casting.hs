{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Casting where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompileWrap)

import Prelude hiding (toInteger, (&&), Ord(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type HRef = Reference Hardware

example :: Hardware ()
example =
  do
{-
     a :: HRef (HExp Word8) <- initRef (value 10)
     b :: HRef (HExp Int8)  <- initRef (value 5)
     c :: HRef (HExp Int16) <- initRef (value 300)

     va <- getRef a
     vb <- getRef b
     vc <- getRef c

     setRef b (i2n va)
     setRef c (i2n va)
     setRef a (i2n vc)

     x0 <- shareM (10 :: HExp Word16)
     for 0 10 $ \(i  :: HExp Integer) ->
       setRef a (i2n (x0 `shiftR` (i * 8)))
-}
     t :: HRef (HExp Word32) <- initRef (value 12)     
     setRef t (k (value 20))

--------------------------------------------------------------------------------

k :: HExp Integer -> HExp Word32
k t = (0  <= t && t <= 19) ?? 0x5a827999 $
      (20 <= t && t <= 39) ?? 0x6ed9eba1 $
      (40 <= t && t <= 59) ?? 0x8f1bbcdc
                            $ 0xca62c1d6
              
(??) :: HExp Bool -> HExp Word32 -> HExp Word32 -> HExp Word32
(??) = (?)
     
--------------------------------------------------------------------------------

test = Hard.icompileWrap example

--------------------------------------------------------------------------------
