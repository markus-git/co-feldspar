{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}
{-# language TypeFamilies #-}

module Tut3_Computational where

import Feldspar
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

import Prelude hiding (length, reverse, div)

--------------------------------------------------------------------------------
-- * Purely computational programs.
--------------------------------------------------------------------------------

-- The previous tutorial's example programs have been restricted to either
-- `Software` or `Hardware` monads and thir respective exprission types 'SExp'
-- and 'HExp'. Its also possible to write programs in such a way that they are
-- independent of whatever monad they eventually will be interpreted as.
--
-- In co-feldspar write such generic programs with the help of overloading.
-- That is, explicit `Software` or `Hardware` types are replaced by constraints
-- and associated types, and programs or expressions are written in the more
-- generic operations provided by the `Feldspar.Frontend` module.
--
-- For example, the square function from Tut2
--
-- > square :: (SType' a, Num a) => SExp a -> SExp a
-- > square a = a * a
--
-- was defined using `SExp`, limiting its use to the `Software` monad.
-- A software/hardware overloaded version can be defined as:

square :: (Syntax exp a, Num (exp a)) => exp a -> exp a
square a = a * a

-- Here the explicit type `SExp` has been replaced by a variable `exp` and
-- the `Num a` and `SType' a` constraints have been replaced by `Num (exp a)`
-- and `Syntax exp a`, respectively.
--
-- - `Num` is still used to ensure `exp` supports multiplication. But with the
-- now variable type we cannot derive `Num (exp a)` from `Num a`, so we must
-- constrain the entire expression instead.
--
-- - `Syntax exp` ensures that our expression type `exp` is a "valid" type and
-- fills the same role as `SType` and `HType`. (Every expression must use such
-- "valid" in order to ensure we can internally build an ASTs around them.)
--
-- The process of defining overloaded programs is very much the same as it was
-- for expressions. That is, swap out specific types for overloaded or associated
-- ones and use the generic front-end provided by the `Feldspar.Frontend` module.
-- 
-- As an example, a generic program for reversing an array of 32-bit integers:

reverse :: forall m .
  ( Monad m      -- Our program type `m` is an monad that supports ...
  , Control m    --  control statements like \for\ and \if\,
  , References m --  references,
  , Arrays m     --  arrays and
  , Loop m       --  for-loops.
  -- As the inner for-loop runs along the entire length of the given array
  -- we make sure that array has a known length.
  , Finite (Expr m) (Array m (Expr m Int32))
  -- To handle the necessary indexing operations, we ensure that there is a
  -- `Num` instance for expressions over indices.
  , Num (Expr m Index)
  -- To support integer division we include a `Multiplicative` constraint.
  , Multiplicative (Expr m)
  -- Any expressions in `m` for 32-bit integers and words should be
  -- a well typed, primitive expression and have a `Syntactic` instance.
  , SyntaxM' m (Expr m Int32)
  , SyntaxM' m (Expr m Word32)
  -- todo: hmm... maybe this should be implied by `SyntaxM'` for `Word32`.
  , Primitive (Expr m) Word32
  )
  => Array m (Expr m Int32) -> m ()
reverse arr =
  do for 0 1 (len `div` 2) $ \ix ->
       do aix <- getArr arr ix
          ajx <- getArr arr (len - ix)
          setArr arr ix         ajx
          setArr arr (len - ix) aix
  where
    len = length arr
-- Note that, as we no longer have use a specific monad like `Software` and
-- `Hardware`, we also can't make use of `SExp` or `HExp`. Instead, we talk
-- about the expression types associated with the monad `m` using `Expr m`.
-- The type `Array m` serves a similar purpose.

--------------------------------------------------------------------------------

-- Seeing as how the `reverse` program consists of only computational
-- instructions we can interperet it as a software program, that is, we can
-- interpret all of its instructions as software instructions.
test1 = Soft.icompile $
  do arr <- initArr [1, 2, 3, 4]
     reverse arr

-- Similarily, the computational instructions of `reverse` can also be
-- interpreted as hardware instructions. So we can interpret `reverse` as a
-- hardware program as well.
test2 = Hard.icompile $
  do arr <- initArr [1, 2, 3, 4]
     reverse arr

--------------------------------------------------------------------------------
