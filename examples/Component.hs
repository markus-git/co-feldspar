{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Component where

import Data.Int
import Data.Word
import Control.Monad

import Feldspar

import Feldspar.Software
import qualified Feldspar.Software as S (icompile)

import Feldspar.Hardware
import qualified Feldspar.Hardware as H (icompile, icompileSig, icompileAXILite)

--------------------------------------------------------------------------------
-- * Example of components in co-feldspar.
--------------------------------------------------------------------------------

plus_impl :: HExp Word32 -> HExp Word32 -> HExp Word32
plus_impl a b = a + b

plus_sig :: HSig (Signal Word32 -> Signal Word32 -> Signal Word32 -> ())
plus_sig =
  input  $ \a ->
  input  $ \b ->
  ret $ pure $ plus_impl a b

test1 = H.icompileAXILite plus_sig

test2 = H.icompileSig plus_sig

--------------------------------------------------------------------------------

type SRef a = Reference Software (SExp a)

plus_soft :: Software ()
plus_soft =
  do plus <- mmap "0x43C00000" plus_sig
     a :: SRef Word32 <- initRef 0
     b :: SRef Word32 <- initRef 1
     c :: SRef Word32 <- newRef
     call plus (a >: b >: c >: nil)
     vc <- getRef c
     printf "plus: %d\n" vc

test3 = S.icompile plus_soft

--------------------------------------------------------------------------------
