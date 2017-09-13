module Feldspar.Software
  ( module Feldspar
  , module Feldspar.Software.Frontend
  , Software
  , Ref, Arr, IArr
  , SExp
  , SType, SType'
  , compile
  , icompile
  ) where

import Feldspar
import Feldspar.Software.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Frontend
import Feldspar.Software.Compile

-- imperative-edsl.
import qualified Language.Embedded.Backend.C  as Imp

--------------------------------------------------------------------------------
-- Interpretation of software programs.
--------------------------------------------------------------------------------

compile :: Software a -> String
compile = Imp.compile . translate

icompile :: Software a -> IO ()
icompile = Imp.icompile . translate

--------------------------------------------------------------------------------
