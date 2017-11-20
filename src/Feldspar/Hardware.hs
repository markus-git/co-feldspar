module Feldspar.Hardware
  ( Hardware
  , Ref, Arr, IArr, SArr, Signal
  , HExp
  , HType, HType', HardwarePrimType
  , module Feldspar
  , module Feldspar.Hardware.Frontend
  , module Feldspar.Hardware.Compile
  ) where

import Feldspar
import Feldspar.Hardware.Representation
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Feldspar.Hardware.Frontend
import Feldspar.Hardware.Compile

-- hardware-edsl
import Language.Embedded.Hardware.Command (Signal)
