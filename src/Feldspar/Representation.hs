{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language TypeOperators #-}
{-# language Rank2Types #-}
{-# language ConstraintKinds #-}

{-# language ScopedTypeVariables #-}

module Feldspar.Representation where

--import Feldspar.Sugar

import Data.Struct
import Data.Inhabited

import Data.Constraint
import Data.Int (Int8)
import Data.List (genericTake)
import Data.Typeable hiding (typeRep, TypeRep)

import Language.Syntactic hiding ((:+:))
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

import Control.Monad.Operational.Higher (Program, Param2, (:+:))

-- imperative-edsl
import qualified Language.Embedded.Imperative.CMD as Imp (Ref, RefCMD, ControlCMD)
import qualified Language.Embedded.Expression     as Imp

-- hardware-edsl
-- ...

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Instructions of a purely computational nature.
type CompCMD = Imp.RefCMD :+: Imp.ControlCMD

-- short-hand for programs made of computational instructions.
type Prog expr pred = Program CompCMD (Param2 expr pred)

-- | Class of monads that support lifting of computational programs.
class Monad m => MonadComp m
  where
    -- | Expressions.
    type Expr m :: * -> *
    -- | Predicate.
    type Pred m :: * -> Constraint
    -- | Representation of types.
    type TRep m :: * -> *

    -- | Lift a computational progam.
    liftComp :: Prog (Expr m) (Pred m) a -> m a

--------------------------------------------------------------------------------
-- * Types.
--------------------------------------------------------------------------------

-- | Representation of supported feldspar types as typed binary trees over
--   primitive types.
type TypeRep pred rep = Struct pred rep

-- | Representation of supported value types and N-ary functions over such
--   types.
data TypeRepF pred rep a
  where
    ValT :: TypeRep pred rep a -> TypeRepF pred rep a
    FunT :: TypeRep pred rep a -> TypeRepF pred rep b -> TypeRepF pred rep (a -> b)

--------------------------------------------------------------------------------

-- | Supported types, that is, types which can be represented as nested pairs of
--   simpler values that respect `pred` and are in turn represented using `trep`.
class (Eq a, Show a, Typeable a, Inhabited a) => Type pred trep a
  where
    typeRep :: TypeRep pred trep a

-- pairs of valid types are themselves also valid types.
instance (Type pred trep a, Type pred trep b) => Type pred trep (a, b)
  where
    typeRep = Branch typeRep typeRep

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

-- | Alternative representation of expressions to expose nesting of values.
class Syntactic a => Structured pred expr a
  where
    construct :: a -> Struct pred expr (Internal a)
    destruct  :: Struct pred expr (Internal a) -> a

-- every syntactical object with a corresponding syntactical instance as a
-- structure can be made an instance of `Structured` by casting with `resugar`.
instance
    ( Syntactic a
    , Syntactic (Struct pred expr (Internal a))
    , Domain    (Struct pred expr (Internal a)) ~ Domain a
    , Internal  (Struct pred expr (Internal a)) ~ Internal a
    )
      => Structured pred expr a
  where
    construct = resugar
    destruct  = resugar

--------------------------------------------------------------------------------

-- short-hand for objects that are well typed and have a nesting we can inspect.
class (Structured (Pred m) (Expr m) a, Type (Pred m) (TRep m) (Internal a)) => Syntax m a

--------------------------------------------------------------------------------
