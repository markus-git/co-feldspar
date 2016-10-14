{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import qualified Feldspar.Software.Compile as Soft

import Feldspar.Hardware
import qualified Feldspar.Hardware.Compile as Hard

import Language.Syntactic (Internal)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

apa :: forall m .
  ( CoMonad m
  , CoType m (Expr m Int8)
       
       -- ugh...
  , Num (Internal (Expr m Int8))
  )
  => m ()
apa = 
  do r <- initRef one
     setRef r (value 2)
     v <- getRef r
     let x = v `plus` value 1
     setRef r x
  where
    one :: Expr m Int8
    one = value 1

--------------------------------------------------------------------------------

bepa :: Software ()
bepa = apa

--------------------------------------------------------------------------------

cepa :: Hardware ()
cepa = apa

--------------------------------------------------------------------------------
