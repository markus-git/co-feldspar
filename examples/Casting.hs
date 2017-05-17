{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Casting where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

type HRef = Reference Hardware

example :: Hardware ()
example =
  do a :: HRef (HExp Word8) <- initRef (value 10)
     b :: HRef (HExp Int8)  <- initRef (value 5)
     c :: HRef (HExp Int16) <- initRef (value 300)

     va <- getRef a
     vb <- getRef b
     vc <- getRef c

     setRef b (i2n va)
     setRef c (i2n va)
     setRef a (i2n vc)

--------------------------------------------------------------------------------
