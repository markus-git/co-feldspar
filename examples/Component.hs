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

plus :: Signal Int32 -> Signal Int32 -> Signal Int32 -> Hardware ()
plus a b c = do
  va <- getSignal a
  vb <- getSignal b
  setSignal c (va + vb)

plus_sig :: HSig (Signal Int32 -> Signal Int32 -> Signal Int32 -> ())
plus_sig = input $ \a -> input $ \b -> output $ \c -> ret $ plus a b c

--------------------------------------------------------------------------------

plus_hard :: Hardware ()
plus_hard = void $ component plus_sig

--------------------------------------------------------------------------------
