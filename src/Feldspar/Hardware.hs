module Feldspar.Hardware
  ( module Feldspar
  , module Feldspar.Hardware.Frontend
  , Hardware
  , Ref, Arr, IArr, SArr, Signal
  , HExp
  , HType, HType', HardwarePrimType
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

-- hardware-edsl
import Language.Embedded.Hardware.Command (Signal)
