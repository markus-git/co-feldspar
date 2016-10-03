{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar
import Feldspar.Software

import Language.Syntactic

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

adder
  :: forall m expr
  .  ( CoMonad m
     , CoType  m (expr Int8)

     , VAL (Domain (expr Int8)) -- ok, but needs to be put in CoType instead of CoMonad.

     , Num (Internal (expr Int8)) -- hmm?
       
     , expr ~ Expr m
     )
  => m ()
adder = do
  let one  = value 1 :: expr Int8

  r <- initRef one

  v <- getRef r

  setRef r (v `plus` one)
  
  return ()

--------------------------------------------------------------------------------
