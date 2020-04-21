{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language MonoLocalBinds #-}

module Tut2_Expressions where

import Feldspar
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

-- hmm...
import Language.Embedded.Hardware.Command (Mode(..))


--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

-- A function that squares its input:
square :: (SType' a, Num a) => SExp a -> SExp a
square a = a * a
-- The type constructor `SExp` is for pure `Software` expressions, where `SExp a`
-- is an expression that will yeild a value of type `a` when evaluated.
-- The type constraint `SType'`

-- Wrapper for `square` that reads a number of \stdin\ and writes its result to
-- \stdout\.
squareProg :: Software ()
squareProg = do
  a :: SExp Int32 <- fget stdin
  printf "square: %d\n" (square a)

test1 = Soft.icompile squareProg

test2 = Soft.runCompiled squareProg

--------------------------------------------------------------------------------

-- A function that doubles its input:
double :: (HType' a, Num a) => HExp a -> HExp a
double a = a * 2
-- The type constructor `HExp` is for pure 'Hardware' expressions.

-- Wrapper for `double` that reads a number of the incoming port and writes its
-- result to outgoing port.
doubleProg :: Hardware ()
doubleProg = undefined -- todo: frontend changed, update example.

test3 = Hard.icompile doubleProg

--------------------------------------------------------------------------------

-- A point of `a` is a pair of two `a`. 
type Point a = (a,a)

-- A small example expression that makes use of points.
pointy :: (SType' a, Num a) => Point (SExp a) -> Point (SExp a) -> SExp a
pointy (a, b) (u, v) = (a - b) * (u - v)

-- Wrapper for `pointy` that reads input and writes output to \stdin\ and
-- \stdout\, respectively.
pointyProg :: Software ()
pointyProg = do
  a :: SExp Int32 <- fget stdin
  b :: SExp Int32 <- fget stdin
  printf "pointy: %d\n" (pointy (a, b) (square a, square b))

test4 = Soft.icompile pointyProg
-- Note that there are no tuples in the generated code, the members of the points
-- simply became seperate variables instead.

--------------------------------------------------------------------------------

-- A function that computes the nth Fibonacci number.
fib :: SExp Word32 -> SExp Word32
fib n = fst $ loop 0 n (0, 1) $ \_ (a, b) -> (b, a + b)
-- The `loop` expression implements a pure for-loop and takes three arguments:
--
-- > The number of iterations.
-- > The initial state.
-- > A step function that computes the next state from the current loop index
--   and current state.
--
-- Furthermore, note that we used regular Haskell tuples to construct and match
-- on the state. This is possible due to the `Syntax` constrain on `loop`:
--
--   loop :: Syntax st => SExp Length -> st -> (SExp Index -> st -> st) -> st
--
-- While we have specifec the type of `loop` here to software expressions, the
-- more general type of `loop` found in the library supports the use of both
-- software and hardware expressions.
--
-- Intuitively, a `Syntax` constraint over some type `a` can be understood as a
-- type that supports translation to and from a Co-Feldspar expression. As an
-- example, the above type of `(SExp Word32, SExp Word32)` is for all intents
-- and purposes the same as `SExp (Word32, Word32)` type. However, the latter
-- type is often preffered, as it can be constructed and matched on by the
-- regular Haskell constructors and functions for tuples.

fibProg :: Software ()
fibProg = do
  a :: SExp Word32 <- fget stdin
  printf "fib of %d: %d\n" a (fib a)

test5 = Soft.icompile fibProg
-- Note that, as in the previous `pointy` example, even as the state of `fib`
-- consisted of a pair of values, there are no tuples in the generated code.


--------------------------------------------------------------------------------
