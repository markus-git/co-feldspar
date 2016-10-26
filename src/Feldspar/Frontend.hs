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

-- short-hand for computational monads that support our basic expressions and commmands.
type CoMonad m =
  ( MonadComp m
  , References m
  , Numerical (Pred m) (Expr m)
  )

-- short-hand for syntactic objects that support lifting values.
type CoType m a =
  ( Syntax m a
  , Value (Pred m) (TRep m) (Domain a)
  )

--------------------------------------------------------------------------------
-- ** Expressions.

class Value pred trep dom | dom -> pred, dom -> trep
  where
    value :: (Type pred trep (Internal a), dom ~ Domain a, Syntactic a) => Internal a -> a 

-- It should be that `dom ~ (sup :&: TypeRepF pred trep)` but I guess the above
-- constraint is easier to read.
--------------------------------------------------------------------------------

-- | Numerical expressions.
class Numerical pred expr | expr -> pred
  where
    plus   :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    minus  :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    times  :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a
    negate :: (pred (Internal (expr a)), Num a) => expr a -> expr a

--------------------------------------------------------------------------------
-- ** Commands.

-- | Commands for managing mutable references.
class MonadComp m => References m
  where
    type Reference m :: * -> *

    initRef :: Syntax m a => a -> m (Reference m a)
    newRef  :: Syntax m a => m (Reference m a)
    getRef  :: Syntax m a => Reference m a -> m a
    setRef  :: Syntax m a => Reference m a -> a -> m ()

--------------------------------------------------------------------------------
