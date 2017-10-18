{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Basic where

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompileWrap)

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

soft :: IO ()
soft = Soft.icompile example

hard :: IO ()
hard = Hard.icompileWrap example

--------------------------------------------------------------------------------
