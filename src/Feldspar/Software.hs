module Feldspar.Software
  ( module Feldspar
  , module Feldspar.Software.Frontend
  , Software
  , Ref, Arr, IArr
  , Address, SArg, Soften, Result, Argument
  , SExp
  , SType, SType'
  , compile
  , icompile
  ) where

import Feldspar
import Feldspar.Common

import Feldspar.Software.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Frontend
import Feldspar.Software.Compile
