{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Component where

import Data.Int
import Data.Word

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile)
  
--------------------------------------------------------------------------------
-- * Example of components in co-feldspar.
--------------------------------------------------------------------------------

plus :: Signal Int32 -> Signal Int32 -> Signal Int32 -> Hardware ()
plus a b c = do
  va <- getSignal a
  vb <- getSignal b
  setSignal c (va + vb)

signature :: Signature (Signal Int32 -> Signal Int32 -> Signal Int32 -> ())
signature = input $ \a -> input $ \b -> output $ \c -> plus a b c

--------------------------------------------------------------------------------

soft :: Software ()
soft = do
  addr <- mmap "0x38C00000" signature
  return ()

--------------------------------------------------------------------------------
