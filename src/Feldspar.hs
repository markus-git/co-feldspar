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

import Data.Inhabited

import Data.Int
import Data.Word hiding (Word)

import Language.Syntactic (Syntactic, Domain, Internal)
