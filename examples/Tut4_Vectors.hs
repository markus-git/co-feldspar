{-# language TypeFamilies        #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Tut4_Vectors where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

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

-- Compute the sum of the square of the numbers from 1 to n:
sumSq :: SExp Word32 -> SExp Word32
sumSq n = sum $ map (\x -> x*x) (1...n :: SPull Word32)
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
dotProd :: ( Num a      -- Lets use any number type instead of `Word32` ...
           , SyntaxM m a -- ... as long as its well-typed in `m`.
           -- Expressions over `Length` must be well typed.
           , SyntaxM' m (Expr m Length)
           , Primitive (Expr m) Length
           -- Expressions must support: 
           , Loop    (Expr m) -- as `sum` uses a loop.
           , Cond    (Expr m) -- as `zip` needs to check with input is smallest.
           , Ordered (Expr m) -- as `zip` needs to compare input lengths.
           )
  => Pull m a -> Pull m a -> a
dotProd a b = sum $ zipWith (*) a b
-- todo: I should put these common constraints in a class like MonadComp.

dotProdProg :: Software ()
dotProdProg =
  do arr :: SArray Word16 <- initArr [1, 2, 3, 4]
     brr :: SPull  Word16 <- toPull <$> unsafeFreezeArr arr

     crr :: SArray Word16 <- initArr [4, 3, 2, 1]
     drr :: SPull  Word16 <- toPull <$> unsafeFreezeArr crr

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
apa :: ( Num a
       , MonadComp m
       , SyntaxM m a
       -- todo: yep, should hide these.
       , Num (Expr m Length)
       , SyntaxM' m (Expr m Length)
       , Primitive (Expr m) Length
       -- hmm...
       , Integral (Internal (Expr m Length))
       )
  => Pull m a -> Push m a
apa vec = reverse vec ++ map (*2) vec

apaProg :: Software ()
apaProg =
  do arr :: SArray  Word16 <- initArr [1, 2, 3, 4]
     brr :: SPull   Word16 <- toPull <$> unsafeFreezeArr arr
     -- todo: hmm... hide or explain mainfest arrays.
     crr :: SIArray Word16 <- manifest <$> manifestFresh (apa brr)
     return ()

test5 = Soft.icompile apaProg

--------------------------------------------------------------------------------

-- Manifest vectors have a direct representation in memory; i.e. they correspond
-- to an array in the generated code. Manifest vectors can be created in
-- different ways; e.g.:
--
-- > By freezing a mutable vector.
-- > By writing another vector to memory using `manifestArr` or `manifestFresh`.
--
-- Writing a vector to memory is often forced by the types. For example, if we
-- want to compose `sumLast5` with `quirk` we find that the types don't match:
manifestApa :: forall m a .
  ( Num a
  , MonadComp m
  , SyntaxM m a
    -- ...
  , Arrays m
  , IArrays m
  , Indexed  (Expr m) (IArray m a)
  , Finite   (Expr m) (Array  m a)
  , Finite   (Expr m) (IArray m a)
  , Slicable (Expr m) (IArray m a)
  , Elem (IArray m a) ~ a
    -- ...
  , Loop    (Expr m)
  , Cond    (Expr m)
  , Ordered (Expr m)
    -- ...
  , Num (Expr m Length)
  , SyntaxM' m (Expr m Length)
  , Primitive (Expr m) Length
    -- hmm...
  , Integral (Internal (Expr m Length))
  )
  => Pull m a -> m a
manifestApa vec =
  do vec2 <- manifestFresh (apa vec)
     -- todo: yep, need to automate this stuff.
     return $ sumLast5' (toPull $ manifest $ vec2)
  where
    sumLast5' :: Pull m a -> a
    sumLast5' = sum . take 5 . reverse
-- Here, `vec2` is a manifest vector. One problem with this example is the use
-- of `manifestFresh` which silently allocates a fresh array to hold the
-- manifest vector. This array will be allocated on the stack and not freed
-- until the end of the current block in the generated code.
--
-- An alternative to `manifestFresh` is `manifestArr` which takes the location
-- to which the vector should be written as an argument. This allows reusing the
-- same array for different manifest vectors. However, such reuse is dangerous
-- since each call to `manifestArr` with a given location will invalidate
-- earlier manifest vectors using that location.

manifestApaProg :: Software ()
manifestApaProg =
  do arr :: SArray  Word16 <- initArr [1, 2, 3, 4]
     brr :: SPull   Word16 <- toPull <$> unsafeFreezeArr arr
     out <- manifestApa brr
     printf "manifest apa: %d\n" out

test6 = Soft.icompile manifestApaProg

--------------------------------------------------------------------------------
