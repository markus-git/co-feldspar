module Feldspar.Software
  ( module Feldspar
  , module Feldspar.Software.Frontend
  , Software
  , Ref, Arr, IArr
  , Args, Result, Argument
  , Addr, Soften
  , SExp
  , SType, SType'
  , compile
  , icompile
  -- todo : should make a struct of these so we can have pairs and such.
  , Signal
  ) where

import Feldspar

import Feldspar.Software.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Frontend
import Feldspar.Software.Compile

import Language.Embedded.Hardware.Command (Signal)
