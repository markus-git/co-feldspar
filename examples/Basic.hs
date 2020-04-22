{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software as Soft
--import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware as Hard
--import Feldspar.Hardware as Hard (icompile)

--------------------------------------------------------------------------------
-- * Basic example of how our hardware software co-design works.
--------------------------------------------------------------------------------

example :: forall m
  . ( MonadComp m
    , SyntaxM m (Expr m Int8)
    -- ...
    , Value (Expr m)
    , Share (Expr m)
    , Num (Expr m Int8)
    )
  => m ()
example = do initRef (exampleExpr :: Expr m Int8); return ()

exampleExpr :: forall expr
   . ( Value expr
     , Share expr
     , Num (expr Int8)
     -- ...
     , Syntax expr (expr Int8)
     )
  => expr Int8
exampleExpr =
  share (5 :: expr Int8) $ \a ->
  share (4 :: expr Int8) $ \b ->
  a + b :: expr Int8

--------------------------------------------------------------------------------

soft1 :: IO ()
soft1 = Soft.icompile example

hard1 :: IO ()
hard1 = Hard.icompile example

--------------------------------------------------------------------------------

type HArr  a = Array  Hardware (HExp a)
type HIArr a = IArray Hardware (HExp a)

dot :: HExp Length -> HExp Length -> HExp Length
    -> HIArr Int32 -> HIArr Int32 -> HExp Int32
dot min max n x b = loop min max 0 (\j sum -> sum + x!j * b!(n-j))

dotC :: Word32 ->
  HSig (Signal Length -> Signal Length -> Signal Index
     -> SArr   Int32  -> SArr   Int32  -> Signal Int32
     -> ())
dotC size =
  input $ \min ->
  input $ \max ->
  input $ \n ->
  inputIArr size $ \x ->
  inputIArr size $ \b ->
  retExpr $ dot min max n x b

test = Hard.icompileSig (dotC 10)

--------------------------------------------------------------------------------
