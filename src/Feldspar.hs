module Feldspar
  ( module Feldspar.Representation
  , module Feldspar.Frontend
  , module Data.Int
  , module Data.Word
  , Inhabited
  , module Language.Syntactic
  ) where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Data.Int
import Data.Word hiding (Word)

-- syntactic.
import Language.Syntactic (Syntactic, Domain, Internal)

-- hardware-edsl.
import Language.Embedded.Hardware.Expression.Represent (Inhabited(..))
