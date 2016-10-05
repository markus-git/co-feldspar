module Feldspar
  ( module Feldspar.Frontend
  , module Data.Int
  , module Data.Word
  , Inhabited
  , Ref
  , MonadComp, Expr, Pred, TRep
  , Type
  , Syntax
  , Syntax' -- todo: get rid off.
  ) where

import Feldspar.Representation
import Feldspar.Frontend

import Data.Inhabited

import Data.Int
import Data.Word
