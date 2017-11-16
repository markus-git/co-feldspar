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
import qualified Feldspar.Hardware as H (icompile, icompileWrap)

--------------------------------------------------------------------------------
-- * Example of components in co-feldspar.
--------------------------------------------------------------------------------

plus :: Signal Int8 -> Signal Int8 -> Signal Int8 -> Hardware ()
plus a b c = do
  va <- getSignal a
  vb <- getSignal b
  setSignal c (va + vb)

plus_sig :: HSig (Signal Int8 -> Signal Int8 -> Signal Int8 -> ())
plus_sig = input $ \a -> input $ \b -> output $ \c -> ret $ plus a b c

--------------------------------------------------------------------------------

plus_hard :: Hardware ()
plus_hard = void $ component plus_sig

test1 = H.icompile plus_hard

--------------------------------------------------------------------------------

type SRef a = Reference Software (SExp a)

plus_soft :: Software ()
plus_soft =
  do plus <- mmap "0x83C00000" plus_sig
     a :: SRef Int8 <- initRef 0
     b :: SRef Int8 <- initRef 1
     c :: SRef Int8 <- newRef
     call plus (a .+. b .+. c .+. empty)
     vc <- getRef c
     printf "plus: %d\n" vc

test2 = S.icompile plus_soft

--------------------------------------------------------------------------------
