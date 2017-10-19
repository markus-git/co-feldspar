{-# language TypeFamilies        #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Tut5_Memory where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

import Prelude hiding (map, zipWith, sum, take, reverse, (++))

--------------------------------------------------------------------------------
-- * Memory manegement.
--------------------------------------------------------------------------------

-- A previous example showed the use of `manifestFresh` to store the content of
-- a vector in memory and get a manifest vector back as result. The problem with
-- this function is that it allocates an array under the hood. Often times,
-- vector operations are done in a "pipeline" consisting of many stages. In such
-- cases, one typically wants to allocate a small number of arrays and use
-- throughout the pipeline.
buildApa_safe :: forall m .
     ( MonadComp m
     , SyntaxM m (Expr m Word32)
     , Value (Expr m)
  -- ok
     , Pully m (Manifest m (Expr m Word32)) (Expr m Word32)
     , Num (Expr m Word32)
  -- ok
     , Manifestable m (Push m (Expr m Word32)) (Expr m Word32)
  -- bad
     , SyntaxM' m (Expr m Length)
     , Primitive (Expr m) Length
     , Num (Internal (Expr m Length))
     , Enum (Internal (Expr m Length))
     , Integral (Internal (Expr m Length))
     )
  => Expr m Word32
  -> m (Manifest m (Expr m Word32))
buildApa_safe n =
  do vec <- listManifest [n]
     vec <- manifestFresh (apa (toPull vec :: Pull m (Expr m Word32)))
     vec <- manifestFresh (apa (toPull vec :: Pull m (Expr m Word32)))
     vec <- manifestFresh (apa (toPull vec :: Pull m (Expr m Word32)))
     vec <- manifestFresh (apa (toPull vec :: Pull m (Expr m Word32)))
     vec <- manifestFresh (apa (toPull vec :: Pull m (Expr m Word32)))
     return vec

buildApa_safeProg :: Software ()
buildApa_safeProg =
  do vec <- buildApa_safe 10
     return ()

test1 = undefined

--------------------------------------------------------------------------------

apa :: ( Num a
       , MonadComp m
       , SyntaxM m a
       , Num (Expr m Length)
       , SyntaxM' m (Expr m Length)
       , Primitive (Expr m) Length
       , Integral (Internal (Expr m Length))
       )
  => Pull m a -> Push m a
apa vec = reverse vec ++ map (*2) vec

--------------------------------------------------------------------------------
