{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Primitive where

import Data.Int
import Data.Word
import Data.Typeable

import Data.Constraint (Dict(..))

import Language.Syntactic
import Language.Syntactic.Functional (Eval(..), EvalEnv, Denotation)

--------------------------------------------------------------------------------
-- * Primitive Types.
--------------------------------------------------------------------------------

-- | Representation of supported primitive types.
data PrimitiveTypeRep a
  where
    -- ^ booleans.
    BoolT   :: PrimitiveTypeRep Bool
    -- ^ signed numbers.
    Int8T   :: PrimitiveTypeRep Int8
--  Int16T  :: PrimitiveTypeRep Int16
--  Int32T  :: PrimitiveTypeRep Int32
--  Int64T  :: PrimitiveTypeRep Int64
    -- ^ unsigned numbers.
    Word8T  :: PrimitiveTypeRep Word8
--  Word16T :: PrimitiveTypeRep Word16
--  Word32T :: PrimitiveTypeRep Word32
--  Word64T :: PrimitiveTypeRep Word64

deriving instance Eq       (PrimitiveTypeRep a)
deriving instance Show     (PrimitiveTypeRep a)
deriving instance Typeable (PrimitiveTypeRep a)

--------------------------------------------------------------------------------

-- | Class of supported primitive types.
class (Eq a, Show a, Typeable a) => PrimitiveType a
  where
    -- | Refiy a primitive type.
    primitiveRep :: PrimitiveTypeRep a

instance PrimitiveType Bool  where primitiveRep = BoolT
instance PrimitiveType Int8  where primitiveRep = Int8T
instance PrimitiveType Word8 where primitiveRep = Word8T

--------------------------------------------------------------------------------

primitiveTypeOf :: PrimitiveType a => a -> PrimitiveTypeRep a
primitiveTypeOf _ = primitiveRep

primitiveTypeEq :: PrimitiveTypeRep a -> PrimitiveTypeRep b -> Maybe (Dict (a ~ b))
primitiveTypeEq BoolT  BoolT  = Just Dict
primitiveTypeEq Int8T  Int8T  = Just Dict
primitiveTypeEq Word8T Word8T = Just Dict
primitiveTypeEq _      _      = Nothing

primitiveTypeWit :: PrimitiveTypeRep a -> Dict (PrimitiveType a)
primitiveTypeWit BoolT  = Dict
primitiveTypeWit Int8T  = Dict
primitiveTypeWit Word8T = Dict

--------------------------------------------------------------------------------
-- * Primitive Expressions.
--------------------------------------------------------------------------------

-- | Primitive symbols.
data Primitive sig
  where
    FreeVar :: String -> Primitive (Full a)
    Lit     :: (Show a, Eq a) => a -> Primitive (Full a)
    -- ^ numerical operations.
    Neg :: Num a => Primitive (a :-> Full a)
    Add :: Num a => Primitive (a :-> a :-> Full a)
    Sub :: Num a => Primitive (a :-> a :-> Full a)
    Mul :: Num a => Primitive (a :-> a :-> Full a)
    -- ^ integral operations.
    Div :: Integral a => Primitive (a :-> a :-> Full a)
    Mod :: Integral a => Primitive (a :-> a :-> Full a)
    -- ^ logical operations.
    Not :: Primitive (Bool :-> Full Bool)
    And :: Primitive (Bool :-> Bool :-> Full Bool)
    -- ^ relational operations.
    Eq  :: Eq a  => Primitive (a :-> a :-> Full Bool)
    Lt  :: Ord a => Primitive (a :-> a :-> Full Bool)

deriving instance Eq       (Primitive a)
deriving instance Show     (Primitive a)
deriving instance Typeable (Primitive a)

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval Primitive
  where
    evalSym (FreeVar v) = error $ "evaluating free variable " ++ show v
    evalSym (Lit a)     = a
    evalSym Neg = negate
    evalSym Add = (+)
    evalSym Sub = (-)
    evalSym Mul = (*)
    evalSym Div = div
    evalSym Mod = mod
    evalSym Not = not
    evalSym And = (&&)
    evalSym Eq  = (==)
    evalSym Lt  = (<=)

instance Symbol Primitive
  where
    symSig (FreeVar v) = signature
    symSig (Lit a)     = signature
    symSig Neg     = signature
    symSig Add     = signature
    symSig Sub     = signature
    symSig Mul     = signature
    symSig Div     = signature
    symSig Mod     = signature
    symSig Not     = signature
    symSig And     = signature
    symSig Eq      = signature
    symSig Lt      = signature

instance Render Primitive
  where
    renderSym  = show
    renderArgs = renderArgsSmart

instance Equality Primitive
  where
    equal s1 s2 = show s1 == show s2

instance StringTree Primitive
instance EvalEnv Primitive env

--------------------------------------------------------------------------------
