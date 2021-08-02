{-# language TypeFamilies        #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Tut4_Vectors where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

import Control.Monad (void)

import Prelude hiding (map, zipWith, sum, take, reverse, (++))

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

-- To simplify our examples' types, we define software specialized arrays.
type SArray  a = Array  Software a -- Regular, software arrays.
type SIArray a = IArray Software a -- Immutable, software arrays.

-- Pull vectors support many list-like operations. Here is a function that sums
-- the last 5 elements in a vector:
sumLast5 :: SPull (SExp Word32) -> SExp Word32
sumLast5 = sum . take 5 . reverse

sumLast5Prog :: Software ()
sumLast5Prog =
  do arr :: SArray (SExp Word32) <- initArr [1, 2, 3, 4] -- Create array.
     brr <- unsafeFreezeArr arr                          -- Make it immutable.
     printf "sum: %d\n" (sumLast5 $ toPull brr)

test1 = Soft.icompile sumLast5Prog
-- Note that all intermediate pull vectors in `sumLast5` have been fused away.
-- The only array in the generated code is the one that holds the input.

test2 = Soft.runCompiled sumLast5Prog

--------------------------------------------------------------------------------

-- Compute the sum of the square of the numbers from 1 to n:
sumSq :: SExp Word32 -> SExp Word32
sumSq n = sum $ map (\x -> x*x) (1...n :: SPull (SExp Word32))
-- The type `Word32` is used quite often our examples, and the vector library as
-- well. As the type is often used, at least on the software side, to represent
-- an index or length, it goes under the aliases: `Index` and `Length`.

sumSqProg :: Software ()
sumSqProg = printf "square sum: %d\n" (sumSq 4)

test3 = Soft.icompile sumSqProg
-- Note that, as with our previous example, there are no arrays declared in the
-- generated code, only scalars.

--------------------------------------------------------------------------------

-- Dot product of two vectors:
dotProd
  :: ( Num a        -- Lets use any number type instead of `SExp Word32`,
     , Syntax exp a -- as long as its well-typed in `exp` and
     , Vector exp   -- `exp` supports the necessary vector expressions.
     )
  => Pull exp a -> Pull exp a -> a
dotProd a b = sum $ zipWith (*) a b

dotProdProg :: Software ()
dotProdProg =
  do arr :: SArray (SExp Word16) <- initArr [1, 2, 3, 4]
     brr :: SPull  (SExp Word16) <- toPull <$> unsafeFreezeArr arr

     crr :: SArray (SExp Word16) <- initArr [4, 3, 2, 1]
     drr :: SPull  (SExp Word16) <- toPull <$> unsafeFreezeArr crr

     printf "dotProd: %d\n" (dotProd brr drr)
-- todo: clean up/automate conversion from/to pull and regular arrays.
     
test4 = Soft.icompile dotProdProg

--------------------------------------------------------------------------------

-- Pull vectors support arbitrary reading patterns. For example, `sumLast5`
-- demonstrated how to read a part from the end of a vector.
--
-- Push vectors, on the other hand, support arbitrary write patterns. For
-- example `++` creates a vector that writes its content using two separate
-- loops -- one for the left operand and one for the right operand.
--
-- The following function appends two modified compies of a vector to each
-- other:
pushy :: (Num a, SyntaxM m a, VectorM m, Loop m, MonadComp m)
  => Pull (Expr m) a -> Push m a
pushy vec = reverse vec ++ map (*2) vec
-- Note that any writing done by a `Push` vector is an stateful operations,
-- it's therefore parameterized by the computational monad `m` in which these
-- writes will be performed (`Pull` vectors do not perform any monadic writes
-- and are therefore only parameterized on their expression's type). As a
-- result, we used the monadic versions of `Syntax` and `Vector`, which are
-- suffixed by an `M` and takes a monadic type instead of an expression type.

pushyProg :: Software ()
pushyProg =
  do arr :: SArray (SExp Word16) <- initArr [1, 2, 3, 4]
     brr :: SPull  (SExp Word16) <- toPull <$> unsafeFreezeArr arr

     -- Apply our pushy vector program to `brr`:
     let crr :: SPush (SExp Word16)
         crr = pushy brr
     
     -- Remember that `Push` arrays only describes how a vector should be
     -- written to some memory. To make the pushy vector manifest, we use
     -- `manifestFresh` operation which writes the vector to a fresh array.
     void $ manifestFresh crr
-- The idea of `manifest` vectors is explained below.

test5 = Soft.icompile pushyProg

--------------------------------------------------------------------------------

-- Manifest vectors have a direct representation in memory; i.e. they correspond
-- to an array in the generated code. Manifest vectors can be created in
-- different ways; e.g.:
--
-- > By freezing a mutable vector.
-- > By writing another vector to memory using `manifestArr` or `manifestFresh`.
--
-- Writing a vector to memory is often forced by the types. For example, if we
-- want to compose `sumLast5` with `pushy` we find that the types don't match:
manifestPushy :: forall m a .
  ( Num a
  , MonadComp m
  , SyntaxM m a
  , VectorM m
  , Loop m
  -- Make sure we can manifest our arrays (todo: maybe put these in `Vector`?).
  , Finite   (Expr m) (Array m a)
  , Slicable (Expr m) (IArray m a)
  -- Make sure the manifest arrays can be used as `pully` vectors.
  , Pully (Expr m) (IArray m a) a
  )
  => Pull (Expr m) a -> m a
manifestPushy vec =
  do -- First we apply `pushy` to vec:
     let arr :: Push m a
         arr = pushy vec
     -- Then, as we need to get a pully vector from our pushy one, we will
     -- need to first manifest it as an array:
     brr <- manifestFresh arr
     -- The manifest array can then be given to our, now generic, `sumLast5`:
     return $ genericSumLast5 brr
  where
    genericSumLast5 :: Pully (Expr m) vec a => vec -> a
    genericSumLast5 = sum . take 5 . reverse
-- Here, `brr` is a manifest vector. One problem with this example is the use
-- of `manifestFresh` which silently allocates a fresh array to hold the
-- manifest vector. This array will be allocated on the stack and not freed
-- until the end of the current block in the generated code.
--
-- An alternative to `manifestFresh` is `manifestArr` which takes the location
-- to which the vector should be written as an argument. This allows reusing the
-- same array for different manifest vectors. However, such reuse is dangerous
-- since each call to `manifestArr` with a given location will invalidate
-- earlier manifest vectors using that location.

manifestPushyProg :: Software ()
manifestPushyProg =
  do arr :: SArray (SExp Word16) <- initArr [1, 2, 3, 4]
     brr :: SPull  (SExp Word16) <- toPull <$> unsafeFreezeArr arr
     
     out <- manifestPushy brr
     
     printf "manifest apa: %d\n" out

test6 = Soft.icompile manifestPushyProg

--------------------------------------------------------------------------------
