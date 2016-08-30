{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language StandaloneDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

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

-- | ...
class Syn a
  where
    type C a :: * -> *
    type I a :: *
    
    desug :: a -> (C a) (I a)
    sug   :: (C a) (I a) -> a

-- | Syntactic type casting.
resug :: (Syn a, Syn b, C a ~ C b, I a ~ I b) => a -> b
resug = sug . desug

--------------------------------------------------------------------------------

class    (Syn a, CoType (I a)) => Syntax a
instance (Syn a, CoType (I a)) => Syntax a

--------------------------------------------------------------------------------
-- **

-- | Associate a syntactic object with its type constraint.
type family PredOf (c :: *) :: (* -> Constraint)

-- | ...
newtype Ref a = Ref { unRef :: Struct (PredOf a) Imp.Ref (I a) }

--------------------------------------------------------------------------------

-- | ...
type CoCMD = Imp.RefCMD Oper.:+: Imp.ControlCMD

--------------------------------------------------------------------------------
