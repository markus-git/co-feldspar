{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language TypeOperators #-}
{-# language Rank2Types #-}
{-# language ConstraintKinds #-}

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

-- imperative-edslJust True
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

-- | ...
type family RepOf (exp :: * -> *) :: * -> *

-- | Class of representable types.
class (Eq a, Show a, Typeable a) => Type exp a
  where
    -- | Reify a type.
    typeRep :: Proxy exp -> TypeRep (PredOf exp) (RepOf exp) a

instance (Type exp a, Type exp b) => Type exp (a, b)
  where
    typeRep p = Branch (typeRep p) (typeRep p)

--------------------------------------------------------------------------------

-- | Alias for the conjunction of `Syntactic` and `Type`.
type Syntax a = (Syntactic a, Type (Constructor a) (Internal a))

--------------------------------------------------------------------------------
{-
asTypeRep :: Struct pred rep a -> TypeRep pred rep a
asTypeRep = mapStruct (const primitiveRep)

typeEq :: TypeRep pred rep a -> TypeRep pred rep b -> Maybe (Dict (a ~ b))
typeEq (Node u)       (Node v)       = undefined
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
-- * ... todo ...
--------------------------------------------------------------------------------

newtype Ref a = Ref { unRef :: Struct (PredOf (Constructor a)) Imp.Ref (Internal a) }

--------------------------------------------------------------------------------

type CoCMD = Imp.RefCMD Oper.:+: Imp.ControlCMD

--------------------------------------------------------------------------------
-- ** ...

class PrimDict expr
  where
    withPrim :: Proxy expr -> Proxy a
      -> (Imp.FreePred expr a => b)
      -> (PredOf expr a => b)

--------------------------------------------------------------------------------
