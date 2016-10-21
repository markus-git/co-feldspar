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

-- | ... short-hand for programs of computational instructions ...
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

    -- | lift a computational progams.
    liftComp :: Prog (Expr m) (Pred m) a -> m a

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

-- | ...
class Expression pred expr a
  where
    construct :: a -> Struct pred expr (Internal a)
    destruct  :: Struct pred expr (Internal a) -> a
{-
-- Every syntactical object with a corresponding syntactical instance for
-- structures can be cast using `resugar`.
instance
    ( Syntactic a
    , Syntactic (Struct pred expr (Internal a))
    , Domain    (Struct pred expr (Internal a)) ~ Domain a
    , Internal  (Struct pred expr (Internal a)) ~ Internal a
    )
      => Expression pred expr a
  where
    construct = resugar
    destruct  = resugar
-}
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

class (Eq a, Show a, Typeable a, Inhabited a) => Type pred trep a
  where
    typeRep :: TypeRep pred trep a

-- Pairs of valid types are themselves also valid types.
instance (Type pred trep a, Type pred trep b) => Type pred trep (a, b)
  where
    typeRep = Branch typeRep typeRep

--------------------------------------------------------------------------------

class (Expression (Pred m) (Expr m) a, Type (Pred m) (TRep m) (Internal a)) => Syntax m a

--------------------------------------------------------------------------------
