{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

{-# language FunctionalDependencies #-}

module Feldspar.Frontend where

import Feldspar.Sugar
import Feldspar.Representation

import Data.Constraint
import Data.Struct
import Data.Proxy

import Language.Syntactic as S

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Short-hand for computational monads that support ...
type CoMonad m =
  ( MonadComp m
    -- ... commands ...
  , References m
    -- ... expressions ...
  , Value     (Pred m) (TRep m) (Expr m)
  , Numerical (Pred m) (Expr m)
  )

--------------------------------------------------------------------------------
-- ** Expressions.

class Value pred rep expr | expr -> pred, pred -> rep
  where
    value :: (Type pred rep (Internal (expr a)), Expression pred expr (expr a)) => a -> expr a

--------------------------------------------------------------------------------

class Numerical pred expr | expr -> pred
  where
    plus   :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    minus  :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    times  :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    negate :: (pred (Internal (expr a)), Num a) => expr a -> expr a

--------------------------------------------------------------------------------
-- ** Commands.

class MonadComp m => References m
  where
    type Reference m :: * -> *

    initRef :: Syntax m a => a -> m (Reference m a)
    newRef  :: Syntax m a => m (Reference m a)
    getRef  :: Syntax m a => Reference m a -> m a
    setRef  :: Syntax m a => Reference m a -> a -> m ()

--------------------------------------------------------------------------------
