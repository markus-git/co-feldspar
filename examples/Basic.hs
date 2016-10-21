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
  , Syntax m (Expr m Int8)
  , Syntax m (Expr m Int8, Expr m Int8)
  )
  => m ()
apa = 
  do let x = value 1 :: Expr m Int8
     let y = value 2 :: Expr m Int8

     r <- initRef (x, y)
     v <- getRef r
     setRef r (y, x)
     
     return ()
  -- Soft.icompile apa
  -- Hard.icompile apa

--------------------------------------------------------------------------------

bepa :: Software ()
bepa = apa
  -- Soft.icompile bepa

--------------------------------------------------------------------------------

cepa :: Hardware ()
cepa = apa
  -- Hard.icompile cepa

--------------------------------------------------------------------------------
