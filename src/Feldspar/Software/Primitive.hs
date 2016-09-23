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

data SoftwarePrimTypeRep a
  where
    -- booleans
    BoolST   :: SoftwarePrimTypeRep Bool
    -- signed numbers.
    Int8ST   :: SoftwarePrimTypeRep Int8
--  Int16ST  :: SoftwarePrimTypeRep Int16
--  Int32ST  :: SoftwarePrimTypeRep Int32
--  Int64ST  :: SoftwarePrimTypeRep Int64
    -- unsigned numbers.
    Word8ST  :: SoftwarePrimTypeRep Word8
--  Word16ST :: SoftwarePrimTypeRep Word16
--  Word32ST :: SoftwarePrimTypeRep Word32
--  Word64ST :: SoftwarePrimTypeRep Word64
    -- floating point numbers.
    FloatST  :: SoftwarePrimTypeRep Float
--  DoulbeST :: SoftwarePrimTypeRep Double

deriving instance Eq       (SoftwarePrimTypeRep a)
deriving instance Show     (SoftwarePrimTypeRep a)
deriving instance Typeable (SoftwarePrimTypeRep a)

--------------------------------------------------------------------------------

-- | Class of supported software types.
class (Eq a, Show a, Typeable a, Inhabited a) => SoftwarePrimType a
  where
    softwareRep :: SoftwarePrimTypeRep a

instance SoftwarePrimType Bool  where softwareRep = BoolST
instance SoftwarePrimType Int8  where softwareRep = Int8ST
instance SoftwarePrimType Word8 where softwareRep = Word8ST
instance SoftwarePrimType Float where softwareRep = FloatST

--------------------------------------------------------------------------------

softwarePrimTypeEq :: SoftwarePrimTypeRep a -> SoftwarePrimTypeRep b -> Maybe (Dict (a ~ b))
softwarePrimTypeEq (BoolST)  (BoolST)  = Just Dict
softwarePrimTypeEq (Int8ST)  (Int8ST)  = Just Dict
softwarePrimTypeEq (Word8ST) (Word8ST) = Just Dict
softwarePrimTypeEq (FloatST) (FloatST) = Just Dict
softwarePrimTypeEq _         _         = Nothing

softwarePrimTypeOf :: SoftwarePrimType a => a -> SoftwarePrimTypeRep a
softwarePrimTypeOf _ = softwareRep

softwarePrimWitType :: SoftwarePrimTypeRep a -> Dict (SoftwarePrimType a)
softwarePrimWitType BoolST  = Dict
softwarePrimWitType Int8ST  = Dict
softwarePrimWitType Word8ST = Dict
softwarePrimWitType FloatST = Dict

--------------------------------------------------------------------------------
-- * ... prim ...
--------------------------------------------------------------------------------

-- | Software primitive symbols.
data SoftwarePrim sig
  where
    FreeVar :: (SoftwarePrimType a)               => String -> SoftwarePrim (Full a)
    Lit     :: (SoftwarePrimType a, Show a, Eq a) => a      -> SoftwarePrim (Full a)
    -- ^ numerical operations.
    Neg     :: (SoftwarePrimType a, Num a)        => SoftwarePrim (a :-> Full a)
    Add     :: (SoftwarePrimType a, Num a)        => SoftwarePrim (a :-> a :-> Full a)
    Sub     :: (SoftwarePrimType a, Num a)        => SoftwarePrim (a :-> a :-> Full a)
    Mul     :: (SoftwarePrimType a, Num a)        => SoftwarePrim (a :-> a :-> Full a)
    -- ^ integral operations.
    Div     :: (SoftwarePrimType a, Integral a)   => SoftwarePrim (a :-> a :-> Full a)
    Mod     :: (SoftwarePrimType a, Integral a)   => SoftwarePrim (a :-> a :-> Full a)
    -- ^ logical operations.
    Not     ::                                       SoftwarePrim (Bool :-> Full Bool)
    And     ::                                       SoftwarePrim (Bool :-> Bool :-> Full Bool)
    -- ^ relational operations.
    Eq      :: (SoftwarePrimType a, Eq a)         => SoftwarePrim (a :-> a :-> Full Bool)
    Lt      :: (SoftwarePrimType a, Ord a)        => SoftwarePrim (a :-> a :-> Full Bool)
    -- ^ geometrical operators.
    Sin     :: (SoftwarePrimType a, Floating a)   => SoftwarePrim (a :-> Full a)
    Cos     :: (SoftwarePrimType a, Floating a)   => SoftwarePrim (a :-> Full a)
    Tan     :: (SoftwarePrimType a, Floating a)   => SoftwarePrim (a :-> Full a)

deriving instance Eq       (SoftwarePrim a)
deriving instance Show     (SoftwarePrim a)
deriving instance Typeable (SoftwarePrim a)

--------------------------------------------------------------------------------

-- | Software primitive symbols.
type SoftwarePrimConstructs = SoftwarePrim

-- | Software primitive symbols tagged with their type representation.
type SoftwarePrimDomain = SoftwarePrimConstructs :&: SoftwarePrimTypeRep

-- | Software primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF SoftwarePrimDomain a }

--------------------------------------------------------------------------------

evalPrim :: Prim a -> a
evalPrim = go . unPrim
  where
    go :: AST SoftwarePrimDomain sig -> Denotation sig
    go (Sym (s :&: _)) = evalSym s
    go (f :$ a)        = go f $ go a

--------------------------------------------------------------------------------

instance Syntactic (Prim a)
  where
    type Domain   (Prim a) = SoftwarePrimDomain
    type Internal (Prim a) = a
    desugar = unPrim
    sugar   = Prim

sugarSymPrim
  :: ( Signature sig
     , fi  ~ SmartFun dom sig
     , sig ~ SmartSig fi
     , dom ~ SmartSym fi
     , dom ~ SoftwarePrimDomain
     , SyntacticN f fi
     , sub :<: SoftwarePrimConstructs
     , SoftwarePrimType (DenResult sig)
     )
  => sub sig -> f
sugarSymPrim = sugarSymDecor softwareRep

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

instance Eval SoftwarePrim
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

instance Symbol SoftwarePrim
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

instance Render SoftwarePrim
  where
    renderSym  = show
    renderArgs = renderArgsSmart

instance Equality SoftwarePrim
  where
    equal s1 s2 = show s1 == show s2

instance StringTree SoftwarePrim
instance EvalEnv SoftwarePrim env

--------------------------------------------------------------------------------
