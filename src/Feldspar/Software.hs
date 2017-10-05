module Feldspar.Software
  ( module Feldspar
  , module Feldspar.Software.Frontend
  , Software
  , Ref, Arr, IArr
  , SExp
  , SType, SType'
  , runIO
  , captureIO
  , compile
  , icompile
  , runCompiled
  , withCompiled
  , compareCompiled
  ) where

import Feldspar
import Feldspar.Software.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Frontend
import Feldspar.Software.Compile
