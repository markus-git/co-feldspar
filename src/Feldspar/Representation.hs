{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language StandaloneDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}
{-# language ScopedTypeVariables #-}
{-# language Rank2Types #-}
{-# language FunctionalDependencies #-}

module Feldspar.Representation where

import Feldspar.Primitive

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2, (:+:))

import Data.Constraint
import Data.Int (Int8)
import Data.List (genericTake)
import Data.Typeable hiding (typeRep, TypeRep)
import Data.Struct

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

-- imperative-edsl
import qualified Language.Embedded.Imperative.CMD as Imp (Ref, RefCMD, ControlCMD)
import qualified Language.Embedded.Expression     as Imp

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | Representation of supported feldspar types as typed binary trees over
--   primitive types.
type TypeRep = Struct PrimitiveType PrimitiveTypeRep

-- | Representation of supported value types and N-ary functions over such
--   types.
data TypeRepF a
  where
    ValT :: TypeRep a -> TypeRepF a
    FunT :: TypeRep a -> TypeRepF b -> TypeRepF (a -> b)

--------------------------------------------------------------------------------

-- | Class of supported feldspar types.
class (Eq a, Show a, Typeable a) => CoType a
  where
    -- | Reify a type.
    typeRep :: TypeRep a

-- any primitive type is a valid feldspar type.
instance (Eq a, Show a, Typeable a, PrimitiveType a) => CoType a
  where
    typeRep = Node primitiveRep

-- pairs of feldspar types are also a valid type.
instance (CoType a, CoType b) => CoType (a, b)
  where
    typeRep = Branch typeRep typeRep

--------------------------------------------------------------------------------

-- | Alias for the conjunction of `PrimitiveType` and `FeldType`.
class    (PrimitiveType a, CoType a) => Type a
instance (PrimitiveType a, CoType a) => Type a

--------------------------------------------------------------------------------

-- | ...
asTypeRep :: Struct PrimitiveType c a -> TypeRep a
asTypeRep = mapStruct (const primitiveRep)

-- | ...
typeEq :: TypeRep a -> TypeRep b -> Maybe (Dict (a ~ b))
typeEq (Node u)       (Node v)       = primitiveTypeEq  u v
typeEq (Branch l1 r1) (Branch l2 r2) = do
  Dict <- typeEq l1 l2
  Dict <- typeEq r1 r2
  return Dict
typeEq _ _ = Nothing

-- | ...
typeEqF :: TypeRepF a -> TypeRepF b -> Maybe (Dict (a ~ b))
typeEqF (ValT u)     (ValT v)     = typeEq u v
typeEqF (FunT l1 r1) (FunT l2 r2) = do
  Dict <- typeEq  l1 l2
  Dict <- typeEqF r1 r2
  return Dict
typeEqF _ _ = Nothing

-- | ...
typeableWit :: TypeRep a -> Dict (Typeable a)
typeableWit (Node u)
  | Dict <- primitiveTypeWit u = Dict
typeableWit (Branch l r)
  | Dict <- typeableWit l
  , Dict <- typeableWit r
  = Dict

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ...
type CoConstructs
  =   Primitive
  -- # extra layer of primitives.
  :+: BindingT -- typed variables.
  :+: Let      -- let bindings.
  :+: Tuple    -- pairs.

-- | ...
type CoDomain = CoConstructs :+: TypeRepF

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | Associate an expression type with its type constraint.
type family PredOf (c :: * -> *) :: (* -> Constraint)

-- | ...
class Syn a
  where
    type C a :: * -> *
    type I a :: *
    desug :: a -> (C a) (I a)
    sug   :: (C a) (I a) -> a
    trep  :: Proxy a -> Struct (PredOf (C a)) PrimitiveTypeRep (I a)

-- | Syntactic type casting.
resug :: (Syn a, Syn b, C a ~ C b, I a ~ I b) => a -> b
resug = sug . desug

{-
instance Syn (Expr a)
  where
    type C (Expr a) = Expr
    type I (Expr a) = a
    desug = sug = id
    ...

instance Sym (Struct Pred Expr a)
  where
    type C (Struct ...) = Expr
    type I (Struct ...) = a
-}
--------------------------------------------------------------------------------

-- | ...
class SynN f internal | f -> internal
  where
    desugN :: f -> internal
    sugN   :: internal -> f

instance {-# overlapping #-} (Syn f, fi ~ (C f) (I f)) => SynN f fi
  where
    desugN = desug
    sugN   = sug

instance {-# overlapping #-} (Syn a, c ~ C a, i ~ I a, SynN f fi) => SynN (a -> f) (c i -> fi)
  where
    desugN f = desugN . f . sug
    sugN   f = sugN . f . desug

--------------------------------------------------------------------------------

class    (Syn a, CoType (I a)) => Syntax a
instance (Syn a, CoType (I a)) => Syntax a

--------------------------------------------------------------------------------
-- **

-- | ...
newtype Ref a = Ref { unRef :: Struct (PredOf (C a)) Imp.Ref (I a) }

-- | ...
type CoCMD = Imp.RefCMD Oper.:+: Imp.ControlCMD

--------------------------------------------------------------------------------
-- **

-- | ...
class PrimDict expr
  where
    withPrim :: Proxy expr -> Proxy a -> (Imp.FreePred expr a => b) -> (PredOf expr a => b)

{-
instance Imp.FreeExp Expr => PrimDict Expr
  where
    withPrim :: Proxy Expr -> Proxy a -> (Imp.FreePred Expr a => b) -> (PrimitiveType => b)
    withPrim p _ f = case freeDict p (primitiveTypeRep :: PrimitiveTypeRep a) of Dict -> f

freeDict :: Proxy Expr -> PrimitiveTypeRep a -> Dict (Imp.FreePred Expr a)
freeDict _ rep = case rep of
  BoolT -> Dict
  ...
-}
--------------------------------------------------------------------------------
