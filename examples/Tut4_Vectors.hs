{-# language ScopedTypeVariables #-}

module Tut4_Vectors where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

import Prelude hiding (sum, take, reverse)

--------------------------------------------------------------------------------
-- * Vectors.
--------------------------------------------------------------------------------
--
-- This file gives an introduction to vectors and some illustrating examples,
-- It is based on the tutorial found in \raw-feldspar\:
-- <https://github.com/Feldspar/raw-feldspar/blob/master/examples/Tut3_Vectors.hs>
--
--------------------------------------------------------------------------------
--
-- The vector library will be used by most Feldspar programs that process data
-- in vector or form. It provides a high-level interface, largely by Haskell's
-- list library.
--
-- The vector library consists of three different vector types:
--
-- > `Manifest`
-- > `Pull`
-- > `Push`
--
-- Each vector type has a different set of operations defined, and the
-- operations are chosen so that each type only supports those which can be
-- carried out rather efficiently for that type.
--
-- Conversion from `Manifest` to `Pull` and from `Pull` to `Push` is always
-- cheap. However, conversion from `Pull`/`Push` to `Manifest` involves writing
-- the whole vector to memory.
--
-- In most cases, the types will guide which type to use when, and conversions
-- are done automatically. For example, `++` is only supported by `Push`, but
-- the operator accepts any two vectors that can be converted to `Push` and it
-- will do the conversion automatically.
--
-- The `Pull` and `Push` types enjoy *guaranteed* fusion. That is, all
-- intermediate vectors of type `Pull` or `Push` are guaranteed not to appear in
-- the generated code. Only `Manifest` vectors will. However, there are cases
-- when fusion leads to duplicated computations, which means that the user may
-- sometimes want to convert to `Manifest` even though this is not demanded by
-- the types.
--
--------------------------------------------------------------------------------

-- To simplify our examples' types, we define software specialized vectors.
type SPull a = Pull Software (SExp a)
type SPush a = Push Software (SExp a)
-- ... and for arrays ...
type SArray  a = Array  Software (SExp a) -- Regular arrays.
type SIArray a = IArray Software (SExp a) -- Immutable arrays.

-- Pull vectors support many list-like operations. Here is a function that sums
-- the last 5 elements in a vector:
sumLast5 :: SPull Word32 -> SExp Word32
sumLast5 = sum . take 5 . reverse

sumLast5Prog :: Software ()
sumLast5Prog =
  do arr :: SArray Word32 <- initArr [1, 2, 3, 4] -- Create example array.
     brr <- unsafeFreezeArr arr                   -- Make it immutable.
     printf "sum: %d\n" (sumLast5 $ toPull brr)

test1 = Soft.icompile sumLast5Prog
-- Note that all intermediate pull vectors in `sumLast5` have been fused away.
-- The only array in the generated code is the one that holds the input.

test2 = Soft.runCompiled sumLast5Prog


--------------------------------------------------------------------------------

ex :: IO ()
ex = Soft.icompile $
  do let len = 5 :: SExp Length
         st  = 0 :: SExp Word32
     printf "ex1: %d\n" (loop len st (\i _ -> i))
     --
     printf "ex2: %d\n" (share st (\i -> share len (\_ -> i)))

--------------------------------------------------------------------------------
