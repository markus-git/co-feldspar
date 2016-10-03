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

-- imperative-edslJust True
import qualified Language.Embedded.Imperative.CMD as Imp (Ref, RefCMD, ControlCMD)
import qualified Language.Embedded.Expression     as Imp

-- hardware-edsl
-- ...

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Instructions of a purely computational nature.
type CompCMD = Imp.RefCMD :+: Imp.ControlCMD

-- | Mutable references.
newtype Ref a = Ref { unRef :: Struct (PredOf (Domain a)) Imp.Ref (Internal a) }

--------------------------------------------------------------------------------

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

type family   ExprOf (syn :: * -> *) :: * -> *
--   instance ExprOf Domain = SData
--   instance ExprOf Data   = SDomain

type family   PredOf (syn :: * -> *) :: * -> Constraint
--   instance PredOf Domain = PrimType
--   instance PredOf Data   = Type

type family   TRepOf (syn :: * -> *) :: * -> *
--   instance TRepOf Domain = PrimRep ?
--   instance TRepOf Data   = Rep

--------------------------------------------------------------------------------

-- | ... to internal representation ...
construct :: Syntax a => a -> Struct (PredOf (Domain a)) (ExprOf (Domain a)) (Internal a)
construct = resugar

-- | ... to sugared representation ...
destruct  :: Syntax a => Struct (PredOf (Domain a)) (ExprOf (Domain a)) (Internal a) -> a
destruct  = resugar

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

class (Eq a, Show a, Typeable a, Inhabited a) => Type dom a
  where
    typeRep :: Proxy dom -> TypeRep (PredOf dom) (TRepOf dom) a

-- Pairs of valid types are themselves also valid types.
instance (Type dom a, Type dom b) => Type dom (a, b)
  where
    typeRep dom = Branch (typeRep dom) (typeRep dom)

--------------------------------------------------------------------------------

class TypeDict dom
  where
    withType :: Proxy dom -> Proxy a -> (Imp.FreePred (ExprOf dom) a => b) -> (PredOf dom a => b)

--------------------------------------------------------------------------------

class ( -- `a` is sugared.
        Syntactic a
        -- `a` can be resugared into a `Struct`.
      , Syntactic (Struct (PredOf (Domain a)) (ExprOf (Domain a)) (Internal a))
      , Domain    (Struct (PredOf (Domain a)) (ExprOf (Domain a)) (Internal a)) ~ Domain a
      , Internal  (Struct (PredOf (Domain a)) (ExprOf (Domain a)) (Internal a)) ~ Internal a
        -- type of `a` is representable and ..
      , Type     (Domain a) (Internal a)
      , TypeDict (Domain a)
        
      , Imp.FreeExp (ExprOf (Domain a))

      )
  => Syntax a

--------------------------------------------------------------------------------

class
  ( -- `a` can be resugared into a struct and has a representable type.
    Syntax a
    -- expression and predicate types associated with `a` is the same as those for `m`.
  , ExprOf (Domain a) ~ Expr m
  , PredOf (Domain a) ~ Pred m
    -- ... `Pred m` should not be `CoType m`, that would be silly.
  , Pred m (Internal a)
  )
  => CoType m a

instance
  ( Syntax a
  , ExprOf (Domain a) ~ Expr m
  , PredOf (Domain a) ~ Pred m
  , PredOf (Domain a) (Internal a)
  )
  => CoType m a

--------------------------------------------------------------------------------
