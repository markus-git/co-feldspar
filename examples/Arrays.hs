{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}

module Arrays where

import Prelude hiding ((<))

import Language.Syntactic (Syntactic(..))

import Feldspar

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompile)

--------------------------------------------------------------------------------
-- * Example of arrays in co-feldspar.
--------------------------------------------------------------------------------

arrays
  :: forall m dom expr
   . ( MonadComp m
     -- ...
     , Finite   (Expr m) (Array  m (Expr m Int8))
     , Indexed  (Expr m) (IArray m (Expr m Int8))
     , Equality (Expr m)
     , Ordered  (Expr m)
     -- ...
     , Num (Expr m Int8)
     , Num (Expr m Length)
     -- ...
     , Elem (IArray m (Expr m Int8)) ~ Expr m Int8
     -- ...
     , SyntaxM' m (Expr m Bool)
     , SyntaxM' m (Expr m Int8)
     , Primitive (Expr m) Int8
     )
  => m ()
arrays =
  do arr :: Array m (Expr m Int8) <- newArr 2
     setArr arr 0 0
     setArr arr 1 1

     v <- getArr arr 1
     ref :: Reference m (Expr m Int8) <- initRef v

     iarr :: IArray m (Expr m Int8) <- freezeArr arr
     iff (v < 2 :: Expr m Bool)
       (setArr arr 1 2)
       (setArr arr 1 3)
     setRef ref (iarr ! (1 :: Expr m Index))
     
--------------------------------------------------------------------------------
