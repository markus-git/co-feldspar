module Feldspar.Hardware
  ( module Feldspar
  , module Feldspar.Hardware.Frontend
  , Hardware
  , Ref, Arr, IArr, SArr, Signal
  , HExp
  , HType, HType'
  , compile
  , icompile
  , icompileWrap
  ) where

import Feldspar
import Feldspar.Hardware.Representation
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Feldspar.Hardware.Frontend
import Feldspar.Hardware.Compile

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal)
import qualified Language.Embedded.Hardware.Command as Hard

--------------------------------------------------------------------------------
-- * Interpretation of hardware programs.
--------------------------------------------------------------------------------

compile :: Hardware a -> String
compile = Hard.compile . translate

icompile :: Hardware a -> IO ()
icompile = Hard.icompile . translate

icompileWrap :: Hardware () -> IO ()
icompileWrap = Hard.icompile . translate . wrap

-- todo: use wrap from hardware-edsl.
wrap :: Hardware () -> Hardware ()
wrap prg = do
  entity       "empty" $ return ()
  architecture "empty" "behav" $
    process [] $ prg

--------------------------------------------------------------------------------
