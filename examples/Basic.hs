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
  , CoType m (Expr m Word8)
       -- ugh...
  , Num (Internal (Expr m Int8))
  , Num (Internal (Expr m Word8))
  )
  => m ()
apa = 
  do r <- initRef (value 1 :: Expr m Int8)
     w <- initRef (value 0 :: Expr m Word8)
     
     setRef r (value 2)
     
     v <- getRef r
     let x = v `plus` value 1
     setRef r x
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
