module Feldspar.Hardware
  ( module Feldspar
  , module Feldspar.Hardware.Frontend
  , Hardware
  , Arr, IArr, SArr
  , Signature, Component, Argument
  , HExp
  , HType, HType'
  , compile
  , icompile
  ) where

import Feldspar

import Feldspar.Hardware.Representation
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Frontend
import Feldspar.Hardware.Compile
