{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Component where

import Data.Int
import Data.Word

import Feldspar

import Feldspar.Software
import Feldspar.Software as S (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as H (icompile)

import qualified Feldspar.Software as S (Ref)
import qualified Feldspar.Hardware as H (Ref)

--------------------------------------------------------------------------------
-- * Example of components in co-feldspar.
--------------------------------------------------------------------------------

plus :: Signal Int32 -> Signal Int32 -> Signal Int32 -> Hardware ()
plus a b c = do
  va <- getSignal a
  vb <- getSignal b
  setSignal c (va + vb)

signature :: Sig (Signal Int32 -> Signal Int32 -> Signal Int32 -> ())
signature = input $ \a -> input $ \b -> output $ \c -> plus a b c

--------------------------------------------------------------------------------

soft :: Software ()
soft = do
  addr <- mmap "0x38C00000" signature
  ra :: S.Ref (SExp Int32) <- newRef
  rb :: S.Ref (SExp Int32) <- newRef
  let args = ra >: rb >: nil
  return ()
{-
  rc :: S.Ref (SExp Int32) <- call addr args
  vc <- getRef rc
  printf "%d" vc
-}
--------------------------------------------------------------------------------
