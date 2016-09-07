{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Software.Primitive where

import Feldspar.Representation
import Data.Struct
import Data.Inhabited

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable hiding (TypeRep)
import Data.Constraint hiding (Sub)

-- syntactic.
import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

-- imperative-edsl.
import Language.Embedded.Expression

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
class (Eq a, Show a, Typeable a, Inhabited a) => SoftwarePrimType a
  where
    softwareRep :: SoftwareTypeRep a

instance SoftwarePrimType Bool  where softwareRep = BoolST
instance SoftwarePrimType Int8  where softwareRep = Int8ST
instance SoftwarePrimType Word8 where softwareRep = Word8ST
instance SoftwarePrimType Float where softwareRep = FloatST

--------------------------------------------------------------------------------

sPrimTypeEq :: SoftwareTypeRep a -> SoftwareTypeRep b -> Maybe (Dict (a ~ b))
sPrimTypeEq (BoolST)  (BoolST)  = Just Dict
sPrimTypeEq (Int8ST)  (Int8ST)  = Just Dict
sPrimTypeEq (Word8ST) (Word8ST) = Just Dict
sPrimTypeEq (FloatST) (FloatST) = Just Dict
sPrimTypeEq _         _         = Nothing

sPrimTypeOf :: SoftwarePrimType a => a -> SoftwareTypeRep a
sPrimTypeOf _ = softwareRep

sPrimWitType :: SoftwareTypeRep a -> Dict (SoftwarePrimType a)
sPrimWitType BoolST  = Dict
sPrimWitType Int8ST  = Dict
sPrimWitType Word8ST = Dict
sPrimWitType FloatST = Dict

--------------------------------------------------------------------------------
-- * ... prim ...
--------------------------------------------------------------------------------

-- | Software primitive symbols.
data SoftwarePrimitive sig
  where
    FreeVar :: (SoftwarePrimType a)               => String -> SoftwarePrimitive (Full a)
    Lit     :: (SoftwarePrimType a, Show a, Eq a) => a -> SoftwarePrimitive (Full a)
    -- ^ numerical operations.
    Neg :: (SoftwarePrimType a, Num a) => SoftwarePrimitive (a :-> Full a)
    Add :: (SoftwarePrimType a, Num a) => SoftwarePrimitive (a :-> a :-> Full a)
    Sub :: (SoftwarePrimType a, Num a) => SoftwarePrimitive (a :-> a :-> Full a)
    Mul :: (SoftwarePrimType a, Num a) => SoftwarePrimitive (a :-> a :-> Full a)
    -- ^ integral operations.
    Div :: (SoftwarePrimType a, Integral a) => SoftwarePrimitive (a :-> a :-> Full a)
    Mod :: (SoftwarePrimType a, Integral a) => SoftwarePrimitive (a :-> a :-> Full a)
    -- ^ logical operations.
    Not :: SoftwarePrimitive (Bool :-> Full Bool)
    And :: SoftwarePrimitive (Bool :-> Bool :-> Full Bool)
    -- ^ relational operations.
    Eq  :: (SoftwarePrimType a, Eq a)  => SoftwarePrimitive (a :-> a :-> Full Bool)
    Lt  :: (SoftwarePrimType a, Ord a) => SoftwarePrimitive (a :-> a :-> Full Bool)
    -- ^ geometrical operators.
    Sin :: (SoftwarePrimType a, Floating a) => SoftwarePrimitive (a :-> Full a)
    Cos :: (SoftwarePrimType a, Floating a) => SoftwarePrimitive (a :-> Full a)
    Tan :: (SoftwarePrimType a, Floating a) => SoftwarePrimitive (a :-> Full a)

deriving instance Eq       (SoftwarePrimitive a)
deriving instance Show     (SoftwarePrimitive a)
deriving instance Typeable (SoftwarePrimitive a)

--------------------------------------------------------------------------------

-- | Software primitive symbols.
type SoftwarePrimitiveConstructs = SoftwarePrimitive

-- | Software primitive symbols tagged with their type representation.
type SoftwarePrimitiveDomain = SoftwarePrimitiveConstructs :&: SoftwareTypeRep

-- | Software primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF SoftwarePrimitiveDomain a }

--------------------------------------------------------------------------------

evalPrim :: Prim a -> a
evalPrim = go . unPrim
  where
    go :: AST SoftwarePrimitiveDomain sig -> Denotation sig
    go (Sym (s :&: _)) = evalSym s
    go (f :$ a)        = go f $ go a

--------------------------------------------------------------------------------
-- ** ...

instance Syntactic (Prim a)
  where
    type Domain   (Prim a) = SoftwarePrimitiveDomain
    type Internal (Prim a) = a
    desugar = unPrim
    sugar   = Prim

--------------------------------------------------------------------------------

sugarSymPrim
  :: ( Signature sig
     , fi  ~ SmartFun dom sig
     , sig ~ SmartSig fi
     , dom ~ SmartSym fi
     , dom ~ SoftwarePrimitiveDomain
     , SyntacticN f fi
     , sub :<: SoftwarePrimitiveConstructs
     , SoftwarePrimType (DenResult sig)
     )
  => sub sig -> f
sugarSymPrim = sugarSymDecor softwareRep

--------------------------------------------------------------------------------

instance (SoftwarePrimType a, Num a) => Num (Prim a)
  where
    fromInteger = constExp . fromInteger
    (+)         = sugarSymPrim Add
    (-)         = sugarSymPrim Sub
    (*)         = sugarSymPrim Mul
    negate      = sugarSymPrim Neg
    abs         = error "Num (Prim a): abs."
    signum      = error "Num (Prim a): signum."

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval SoftwarePrimitive
  where
    evalSym (FreeVar v) = error $ "evaluating free variable " ++ show v
    evalSym (Lit a)     = a
    evalSym Neg         = negate
    evalSym Add         = (+)
    evalSym Sub         = (-)
    evalSym Mul         = (*)
    evalSym Div         = div
    evalSym Mod         = mod
    evalSym Not         = not
    evalSym And         = (&&)
    evalSym Eq          = (==)
    evalSym Lt          = (<=)
    evalSym Sin         = sin
    evalSym Cos         = cos
    evalSym Tan         = tan

instance Symbol SoftwarePrimitive
  where
    symSig (FreeVar v) = signature
    symSig (Lit a)     = signature
    symSig Neg         = signature
    symSig Add         = signature
    symSig Sub         = signature
    symSig Mul         = signature
    symSig Div         = signature
    symSig Mod         = signature
    symSig Not         = signature
    symSig And         = signature
    symSig Eq          = signature
    symSig Lt          = signature
    symSig Sin         = signature
    symSig Cos         = signature
    symSig Tan         = signature

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

instance FreeExp Prim
  where
    type FreePred Prim = SoftwarePrimType
    constExp = sugarSymPrim . Lit
    varExp   = sugarSymPrim . FreeVar

instance EvalExp Prim
  where
    evalExp = evalPrim

--------------------------------------------------------------------------------
