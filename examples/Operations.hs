{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile)

import Prelude hiding (mod)

--------------------------------------------------------------------------------
-- * Hardware
--------------------------------------------------------------------------------

type HRef = Reference Hardware

hex :: Hardware ()
hex =
  do a :: HRef (HExp Word8) <- initRef 10
     b :: HRef (HExp Word8) <- newRef

     va <- getRef a
     setRef b (va `mod` 2)

--------------------------------------------------------------------------------

htest = Hard.icompile hex

--------------------------------------------------------------------------------
