{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language ConstraintKinds #-}

module Feldspar.Representation
  (
  -- short-hands.
    Length
  , Index
  -- type representations.
  , TypeRep(..)
  , TypeRepF(..)
  -- types.
  , Type(..)
  , PrimType
  -- type families.
  , Expr
  , Pred
  -- external.
  , Inhabited(..)
  -- hmm...
  , ExprOf
  , PredOf
  , DomainOf
  , RepresentationOf
  ) where

import Data.Struct

import Data.Constraint
import Data.Word
import Data.List (genericTake)
import Data.Typeable hiding (typeRep, TypeRep)

-- syntactic.
import Language.Syntactic hiding ((:+:))
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

-- hardware-edsl.
import Language.Embedded.Hardware.Expression.Represent (Inhabited(..))

-- operational-higher.
import Control.Monad.Operational.Higher (ProgramT, Param2)

--------------------------------------------------------------------------------
-- * Co-Feldspar types.
--------------------------------------------------------------------------------

-- | Expression associated with a program monad.
type family Expr (m :: * -> *) :: * -> *

-- | Predicate associated with a program monad.
type family Pred (m :: * -> *) :: * -> Constraint

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
  
-- | Supported types, that is, types which can be represented as nested pairs of
--   simpler values that respect `pred` and are in turn represented using `trep`.
class (Eq a, Show a, Typeable a, Inhabited a) => Type pred a
  where
    typeRep :: TypeRep pred (RepresentationOf pred) a

-- | Pairs of valid types are themselves also valid types.
instance (Type pred a, Type pred b) => Type pred (a, b)
  where
    typeRep = Branch typeRep typeRep

-- | Pairs of inhabited types are also inhabited.
instance (Inhabited a, Inhabited b) => Inhabited (a, b)
  where
    reset = (reset, reset)

-- | Short-hand for supported types that also respect their primitive constraint.
class    (Type pred a, pred a) => PrimType pred a
instance (Type pred a, pred a) => PrimType pred a

--------------------------------------------------------------------------------
-- Short-hand for common data types.

type Length = Word32
type Index  = Word32

--------------------------------------------------------------------------------
-- hmm...

type family ExprOf (val :: *) :: * -> *

type family PredOf (exp :: * -> *) :: * -> Constraint

type family DomainOf (exp :: * -> *) :: * -> *

type family RepresentationOf (pred :: * -> Constraint) :: * -> *

--------------------------------------------------------------------------------
