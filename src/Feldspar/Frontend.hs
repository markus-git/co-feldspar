{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

{-# language FunctionalDependencies #-}

{-# language TypeOperators #-}

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
-- * Frontend.
--------------------------------------------------------------------------------

-- | Short-hand for a `Syntactic` instance over typed pritmitive values from `dom`.
type Syntax' dom a = (Syntactic a, Type (Pred dom) (Internal a), dom ~ Domain a)

--------------------------------------------------------------------------------
-- ** Expressions.

-- | Literals.
class Value dom
  where
    value :: Syntax' dom a => Internal a -> a

--------------------------------------------------------------------------------

-- | Forced evaluation.
class Share dom
  where
    share :: (Syntax' dom a, Syntax' dom b)
      => a        -- ^ Value to share.
      -> (a -> b) -- ^ Body in which to share the value.
      -> b

--------------------------------------------------------------------------------

-- | Conditional statements.
class Boolean dom
  where
    bool
      :: ( Syntax' dom a, Syntax' dom b, Internal b ~ Bool)
      => a -- ^ true branch.
      -> a -- ^ false branch.
      -> b -- ^ condition.
      -> a
    false :: (Syntax' dom a, Internal a ~ Bool) => a
    true  :: (Syntax' dom a, Internal a ~ Bool) => a

--------------------------------------------------------------------------------
-- ** ...



--------------------------------------------------------------------------------
-- ** Commands.
{-
-- | Commands for managing mutable references.
class Monad m => References m
  where
    type Reference m :: * -> *

    initRef :: Syntax m a => a -> m (Reference m a)
    newRef  :: Syntax m a => m (Reference m a)
    getRef  :: Syntax m a => Reference m a -> m a
    setRef  :: Syntax m a => Reference m a -> a -> m ()
-}
--------------------------------------------------------------------------------
