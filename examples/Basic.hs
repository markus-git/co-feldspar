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

-- | ...
apa :: forall m expr pred trep
  .  ( expr ~ Expr m
     , pred ~ Pred m
     , trep ~ TRep m
    
     , CoMonad m
     , CoType  m (expr Int8)

       -- since we can't assume (Internal (expr a) ~ a),
       -- or maybe we can... but it's not pretty.
       -- > Say `Num a => Num (Internal (expr a))` instead?
       --   but then we can only define fromInteger...
     , Num (Internal (expr Int8))
     )
  => m ()
apa = 
  do r <- initRef one
     setRef r (value 2)
     v <- getRef r
     let x = v `plus` value 1
     setRef r x
  where
    one :: expr Int8
    one = value 1

--------------------------------------------------------------------------------

bepa :: Software ()
bepa = apa

--------------------------------------------------------------------------------
    
-- ...

--------------------------------------------------------------------------------
