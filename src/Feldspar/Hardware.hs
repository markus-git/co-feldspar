module Feldspar.Hardware
  ( module Feldspar
  , module Feldspar.Hardware.Frontend
  , Hardware
  , Ref, Arr, IArr, SArr, Signal
  , Sig, HArg
  , HExp
  , HType, HType'
  , compile
  , icompile
  ) where

import Feldspar
import Feldspar.Common

import Feldspar.Hardware.Representation
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Frontend
import Feldspar.Hardware.Compile

import Language.Embedded.Hardware.Command (Signal)
