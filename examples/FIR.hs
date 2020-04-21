{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

module FIR where

import Feldspar
import Feldspar.Array.Vector hiding ((++))
import Feldspar.Array.Buffered

import Feldspar.Software
import Feldspar.Software as Soft (icompile,compile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile,compile,compileAXILite)

import Data.Int
import Data.Word

import Prelude hiding (min,length,(>=),(<))

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

type HRef    a = Reference Hardware (HExp a)
type HArray  a = Array  Hardware (HExp a)
type HIArray a = IArray Hardware (HExp a)

type SRef    a = Reference Software (SExp a)
type SArray  a = Array  Software (SExp a)
type SIArray a = IArray Software (SExp a)

--------------------------------------------------------------------------------

type CompE exp =
  ( Cond    exp
  , Ordered exp
  , Iterate exp
  , Num (exp Int32)
  , Num (exp Word32)
  , Syntax exp (exp Int32)
  , Syntax exp (exp Word32)
  , Primitive exp Word32
  , Internal (exp Word32) ~ Word32
  )

type VecE arr exp =
  ( Finite  exp (arr (exp Int32))
  , Indexed exp (arr (exp Int32))
  , ArrElem     (arr (exp Int32))  ~ exp Int32
  )

dot :: (CompE exp, VecE arr exp)
  => exp Length      -> exp Length      -> exp Index
  -> arr (exp Int32) -> arr (exp Int32) -> exp Int32
dot min max n x b = loop min max 0 (\j sum -> sum + x!j * b!(n-j))

dotC :: HSig (
     Signal Length -> Signal Length -> Signal Index
  -> SArr   Int32  -> SArr   Int32  -> Signal Int32
  -> ())
dotC =
  input $ \min -> input $ \max -> input $ \n ->
  inputIArr size $ \x -> inputIArr size $ \b ->
  retExpr $ dot min max n x b

dotS ::
    SRef Length -> SRef Length -> SExp Index
 -> SIArray Int32 -> SIArray Int32
 -> Software (SExp Int32)
dotS min max n x b = do
  dot <- mmap "0x43C00000" dotC
  res <- newRef
  n'  <- initRef n
  x'  <- unsafeThawArr x
  b'  <- unsafeThawArr b
  call dot (min >: max >: n' >: x' >>: b' >>: res >: nil)
  getRef res

firO :: forall m . (CompM m, m ~ Software)
  => IArray m (Expr m Int32)
  -> IArray m (Expr m Int32)
  -> m (Array m (Expr m Int32))
firO x b = do
  let l' = length x
      n' = length b
  ys  :: Array m (Expr m Int32)      <- newArr (l' + n')
  for 0 1 l' $ \(n :: Expr m Word32) -> do
    min <- initRef (n >= n'-1 ? n-n'-1 $ 0)
    max <- initRef (n+1 < l' ? n+1 $ l')
    v   <- dotS min max n x b
    setArr ys n v
  return ys

--------------------------------------------------------------------------------

type CompM m =
  ( CompE (Expr m)
  , VecE  (IArray m) (Expr m)
  , Loop m
  , Arrays m
  , IArrays m
  , References m
  )

fir :: forall m . (CompM m)
  => IArray m (Expr m Int32)
  -> IArray m (Expr m Int32)
  -> m (Array m (Expr m Int32))
fir x b = do
  let l' = length x
      n' = length b
  y   :: Array m (Expr m Int32)      <- newArr (l' + n')
  for 0 1 l' $ \(n :: Expr m Word32) -> do
    min <- shareM (n >= n'-1 ? n-n'-1 $ 0)
    max <- shareM (n+1 < l' ? n+1 $ l')
    setArr y n (dot min max n x b)
  return y

firC :: HSig (SArr Int32 -> SArr Int32 -> SArr Int32 -> ())
firC =
  inputIArr size $ \x ->
  inputIArr size $ \b ->
  retVArr (size*2-1) $
    fir x b

firS ::
     SIArray Int32
  -> SIArray Int32
  -> Software (SArray Int32)
firS x b = do
  fir <- mmap "0x43C00000" firC
  y   :: SArray Int32 <- newArr (value (size*2-1))
  x'  <- unsafeThawArr x
  b'  <- unsafeThawArr b
  call fir (x' >>: b' >>: y >>: nil)
  return y

--------------------------------------------------------------------------------

test = test_dotC >> test_dotS >> test_firC >> test_firS

test_dotC = writeFile ("dot" ++ show size ++ ".vhd") (Hard.compileAXILite dotC)
test_dotS = writeFile ("dot" ++ show size ++ ".c") (Soft.compile prog)
  where
    prog :: Software ()
    prog = do
      a :: SIArray Int32 <- unsafeFreezeArr =<< initArr [1..sizeI]
      b :: SIArray Int32 <- unsafeFreezeArr =<< initArr [1..sizeI]
      c :: SIArray Int32 <- unsafeFreezeArr =<< firO a b
      printf "val: %d\n" (c ! (0::SExp Index))

test_firC = writeFile ("fir" ++ show size ++ ".vhd") (Hard.compileAXILite firC)
test_firS = writeFile ("fir" ++ show size ++ ".c") (Soft.compile prog)
  where
    prog :: Software ()
    prog = do
      a :: SIArray Int32 <- unsafeFreezeArr =<< initArr [1..sizeI]
      b :: SIArray Int32 <- unsafeFreezeArr =<< initArr [1..sizeI]
      c :: SIArray Int32 <- unsafeFreezeArr =<< firS a b
      printf "val: %d\n" (c ! (0::SExp Index))

size  = 20 :: Word32
sizeI = 20 :: Int32
