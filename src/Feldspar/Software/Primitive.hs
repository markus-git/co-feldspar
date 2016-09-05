{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

module Feldspar.Software.Primitive where

import Feldspar.Primitive
import Feldspar.Representation
import Data.Struct

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable hiding (TypeRep)

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

--------------------------------------------------------------------------------
-- * Software Types.
--------------------------------------------------------------------------------

data SoftwareTypeRep a
  where
    -- booleans
    BoolST   :: SoftwareTypeRep Bool
    -- signed numbers.
    Int8ST   :: SoftwareTypeRep Int8
--  Int16ST  :: SoftwareTypeRep Int16
--  Int32ST  :: SoftwareTypeRep Int32
--  Int64ST  :: SoftwareTypeRep Int64
    -- unsigned numbers.
    Word8ST  :: SoftwareTypeRep Word8
--  Word16ST :: SoftwareTypeRep Word16
--  Word32ST :: SoftwareTypeRep Word32
--  Word64ST :: SoftwareTypeRep Word64
    -- floating point numbers.
    FloatST  :: SoftwareTypeRep Float
--  DoulbeST :: SoftwareTypeRep Double

deriving instance Eq       (SoftwareTypeRep a)
deriving instance Show     (SoftwareTypeRep a)
deriving instance Typeable (SoftwareTypeRep a)

--------------------------------------------------------------------------------

-- | Class of supported software types.
class (Eq a, Show a, Typeable a) => SoftwarePrimType a
  where
    softwareRep :: SoftwareTypeRep a

instance SoftwarePrimType Bool  where softwareRep = BoolST
instance SoftwarePrimType Int8  where softwareRep = Int8ST
instance SoftwarePrimType Word8 where softwareRep = Word8ST
instance SoftwarePrimType Float where softwareRep = FloatST

--------------------------------------------------------------------------------
-- * ... prim ...
--------------------------------------------------------------------------------

-- | Software primitive symbols.
data SoftwarePrimitive sig
  where
    -- ^ geometrical operators.
    Sin :: Floating a => SoftwarePrimitive (a :-> Full a)
    Cos :: Floating a => SoftwarePrimitive (a :-> Full a)
    Tan :: Floating a => SoftwarePrimitive (a :-> Full a)

deriving instance Eq       (SoftwarePrimitive a)
deriving instance Show     (SoftwarePrimitive a)
deriving instance Typeable (SoftwarePrimitive a)

--------------------------------------------------------------------------------

-- | Software primitive symbols.
type SoftwarePrimitiveConstructs = SoftwarePrimitive :+: Primitive

-- | Software primitive symbols tagged with their type representation.
type SoftwarePrimitiveDomain = SoftwarePrimitiveConstructs :&: TypeRepF SoftwarePrimType SoftwareTypeRep

-- | Software primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF SoftwarePrimitiveDomain a }

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval SoftwarePrimitive
  where
    evalSym Sin = sin
    evalSym Cos = cos
    evalSym Tan = tan

instance Symbol SoftwarePrimitive
  where
    symSig Sin = signature
    symSig Cos = signature
    symSig Tan = signature

instance Render SoftwarePrimitive
  where
    renderSym  = show
    renderArgs = renderArgsSmart

instance Equality SoftwarePrimitive
  where
    equal s1 s2 = show s1 == show s2

instance StringTree SoftwarePrimitive
instance EvalEnv SoftwarePrimitive env

--------------------------------------------------------------------------------
