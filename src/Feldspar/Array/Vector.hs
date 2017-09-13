{-# language GADTs #-}

module Feldspar.Array.Vector where

import Feldspar
import Feldspar.Frontend (Arrays)

--------------------------------------------------------------------------------
-- * 1-dimensional vector library.
--------------------------------------------------------------------------------
--
-- This library has been inspired by the vector library in rawfeldspar
-- <https://github.com/Feldspar/raw-feldspar>
--
-- The general idea of pull and push vectors is described in
-- "Combining deep and shallow embedding of domain-specific languages"
-- <http://dx.doi.org/10.1016/j.cl.2015.07.003>.
--
-- Push arrays were originally introduced in
-- "Expressive array constructs in an embedded GPU kernel programming language"
-- <http://dx.doi.org/10.1145/2103736.2103740>.
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Manifest vectors.

-- | A 1-dimensional vector with a concrete representation in memory
type Manifest m = Array m

--------------------------------------------------------------------------------
-- ** Pull vectors.

-- | 1-dimensional pull vector: a vector representation that supports random
--   access and fusion of operations.
data Pull m a where
    Pull :: Expr m Length        -- ^ Length of vector.
         -> (Expr m Index -> a)  -- ^ Index function.
         -> Pull m a

instance Functor (Pull m)
  where
    fmap f (Pull len ixf) = Pull len (f . ixf)

--instance Indexed (DomainOf m)

--------------------------------------------------------------------------------
