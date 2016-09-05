{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# language Rank2Types #-}

module Feldspar.Representation where

import Feldspar.Primitive
import Feldspar.Sugar
import Data.Struct

import Data.Constraint
import Data.Int (Int8)
import Data.List (genericTake)
import Data.Typeable hiding (typeRep, TypeRep)

import Language.Syntactic hiding (Syntactic(..), SyntacticN(..))
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2, (:+:))

-- imperative-edsl
import qualified Language.Embedded.Imperative.CMD as Imp (Ref, RefCMD, ControlCMD)
import qualified Language.Embedded.Expression     as Imp

-- hardware-edsl
-- ...

--------------------------------------------------------------------------------
-- * ...
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

-- | Short-hand for representation of primitive types.
type PrimTypeRep = TypeRep PrimitiveType PrimitiveTypeRep

-- | Class of supported co-design types.
class (Eq a, Show a, Typeable a) => CoType a
  where    
    -- | Reify a type.
    typeRep :: PrimTypeRep a

-- any primitive type is a valid co-design type.
instance (Eq a, Show a, Typeable a, PrimitiveType a) => CoType a
  where    
    typeRep = Node primitiveRep

-- any pair of valid co-design types is also a valid type.
instance (CoType a, CoType b) => CoType (a, b)
  where    
    typeRep = Branch typeRep typeRep

--------------------------------------------------------------------------------

-- | Alias for the conjunction of `PrimitiveType` and `FeldType`.
class    (PrimitiveType a, CoType a) => Type a
instance (PrimitiveType a, CoType a) => Type a

-- | Alias for the conjunction of `Syntactic` and `CoType`.
class    (Syntactic a, CoType (Internal a)) => Syntax a
instance (Syntactic a, CoType (Internal a)) => Syntax a

--------------------------------------------------------------------------------
-- ** ... generalize to type representations other than primitive ones ...
{-
asTypeRep :: Struct PrimitiveType c a -> TypeRep a
asTypeRep = mapStruct (const primitiveRep)

typeEq :: TypeRep a -> TypeRep b -> Maybe (Dict (a ~ b))
typeEq (Node u)       (Node v)       = primitiveTypeEq  u v
typeEq (Branch l1 r1) (Branch l2 r2) = do
  Dict <- typeEq l1 l2
  Dict <- typeEq r1 r2
  return Dict
typeEq _ _ = Nothing

typeEqF :: TypeRepF a -> TypeRepF b -> Maybe (Dict (a ~ b))
typeEqF (ValT u)     (ValT v)     = typeEq u v
typeEqF (FunT l1 r1) (FunT l2 r2) = do
  Dict <- typeEq  l1 l2
  Dict <- typeEqF r1 r2
  return Dict
typeEqF _ _ = Nothing

typeableWit :: TypeRep a -> Dict (Typeable a)
typeableWit (Node u)
  | Dict <- primitiveTypeWit u = Dict
typeableWit (Branch l r)
  | Dict <- typeableWit l
  , Dict <- typeableWit r
  = Dict
-}

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

newtype Ref a = Ref { unRef :: Struct (PredOf (Constructor a)) Imp.Ref (Internal a) }

--------------------------------------------------------------------------------
-- ** ...

type CoConstructs
  =   Primitive
  -- ^ extra layer of primitives.
  :+: BindingT -- typed variables.
  :+: Let      -- let bindings.
  :+: Tuple    -- pairs.

type CoDomain = CoConstructs :&: TypeRepF PrimitiveType PrimitiveTypeRep

--------------------------------------------------------------------------------
-- ** ...

type CoCMD = Imp.RefCMD Oper.:+: Imp.ControlCMD

--------------------------------------------------------------------------------
-- ** ...

class PrimDict expr
  where
    withPrim :: Proxy expr -> Proxy a
      -> (Imp.FreePred expr a => b)
      -> (PredOf expr a => b)

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
