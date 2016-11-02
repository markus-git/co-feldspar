{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Hardware.Primitive where

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
--import Language.Embedded.Expression

-- hardware-edsl.
import Language.Embedded.Hardware.Interface

--------------------------------------------------------------------------------
-- * Hardware Types.
--------------------------------------------------------------------------------

data HardwarePrimTypeRep a
  where
    -- booleans
    BoolHT   :: HardwarePrimTypeRep Bool
    -- signed numbers.
    Int8HT   :: HardwarePrimTypeRep Int8
--  Int16HT  :: HardwarePrimTypeRep Int16
--  Int32HT  :: HardwarePrimTypeRep Int32
--  Int64HT  :: HardwarePrimTypeRep Int64
    -- unsigned numbers.
    Word8HT  :: HardwarePrimTypeRep Word8
--  Word16HT :: HardwarePrimTypeRep Word16
--  Word32HT :: HardwarePrimTypeRep Word32
--  Word64HT :: HardwarePrimTypeRep Word64

deriving instance Eq       (HardwarePrimTypeRep a)
deriving instance Show     (HardwarePrimTypeRep a)
deriving instance Typeable (HardwarePrimTypeRep a)

--------------------------------------------------------------------------------

-- | Class of supported software types.
class (Eq a, Show a, Typeable a, Inhabited a) => HardwarePrimType a
  where
    hardwareRep :: HardwarePrimTypeRep a

instance HardwarePrimType Bool  where hardwareRep = BoolHT
instance HardwarePrimType Int8  where hardwareRep = Int8HT
instance HardwarePrimType Word8 where hardwareRep = Word8HT

--------------------------------------------------------------------------------

hardwarePrimTypeEq :: HardwarePrimTypeRep a -> HardwarePrimTypeRep b -> Maybe (Dict (a ~ b))
hardwarePrimTypeEq (BoolHT)  (BoolHT)  = Just Dict
hardwarePrimTypeEq (Int8HT)  (Int8HT)  = Just Dict
hardwarePrimTypeEq (Word8HT) (Word8HT) = Just Dict
hardwarePrimTypeEq _         _         = Nothing

hardwarePrimTypeOf :: HardwarePrimType a => a -> HardwarePrimTypeRep a
hardwarePrimTypeOf _ = hardwareRep

hardwarePrimWitType :: HardwarePrimTypeRep a -> Dict (HardwarePrimType a)
hardwarePrimWitType BoolHT  = Dict
hardwarePrimWitType Int8HT  = Dict
hardwarePrimWitType Word8HT = Dict

--------------------------------------------------------------------------------
-- * ... prim ...
--------------------------------------------------------------------------------

-- | Hardware primitive symbols.
data HardwarePrim sig
  where
    FreeVar :: (HardwarePrimType a) => String -> HardwarePrim (Full a)
    Lit     :: (Show a, Eq a)       => a      -> HardwarePrim (Full a)
    -- ^ numerical operations.
    Neg     :: (HardwarePrimType a, Num a)        => HardwarePrim (a :-> Full a)
    Add     :: (HardwarePrimType a, Num a)        => HardwarePrim (a :-> a :-> Full a)
    Sub     :: (HardwarePrimType a, Num a)        => HardwarePrim (a :-> a :-> Full a)
    Mul     :: (HardwarePrimType a, Num a)        => HardwarePrim (a :-> a :-> Full a)
    -- ^ integral operations.
    Div     :: (HardwarePrimType a, Integral a)   => HardwarePrim (a :-> a :-> Full a)
    Mod     :: (HardwarePrimType a, Integral a)   => HardwarePrim (a :-> a :-> Full a)
    -- ^ logical operations.
    Not     ::                                       HardwarePrim (Bool :-> Full Bool)
    And     ::                                       HardwarePrim (Bool :-> Bool :-> Full Bool)
    -- ^ relational operations.
    Eq      :: (HardwarePrimType a, Eq a)         => HardwarePrim (a :-> a :-> Full Bool)
    Lt      :: (HardwarePrimType a, Ord a)        => HardwarePrim (a :-> a :-> Full Bool)

deriving instance Eq       (HardwarePrim a)
deriving instance Show     (HardwarePrim a)
deriving instance Typeable (HardwarePrim a)

--------------------------------------------------------------------------------

-- | Hardware primitive symbols.
type HardwarePrimConstructs = HardwarePrim

-- | Hardware primitive symbols tagged with their type representation.
type HardwarePrimDomain = HardwarePrimConstructs :&: HardwarePrimTypeRep

-- | Hardware primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF HardwarePrimDomain a }

--------------------------------------------------------------------------------

evalPrim :: Prim a -> a
evalPrim = go . unPrim
  where
    go :: AST HardwarePrimDomain sig -> Denotation sig
    go (Sym (s :&: _)) = evalSym s
    go (f :$ a)        = go f $ go a

--------------------------------------------------------------------------------

instance Syntactic (Prim a)
  where
    type Domain   (Prim a) = HardwarePrimDomain
    type Internal (Prim a) = a
    desugar = unPrim
    sugar   = Prim

sugarSymPrim
  :: ( Signature sig
     , fi  ~ SmartFun dom sig
     , sig ~ SmartSig fi
     , dom ~ SmartSym fi
     , dom ~ HardwarePrimDomain
     , SyntacticN f fi
     , sub :<: HardwarePrimConstructs
     , HardwarePrimType (DenResult sig)
     )
  => sub sig -> f
sugarSymPrim = sugarSymDecor hardwareRep

--------------------------------------------------------------------------------

instance FreeExp Prim
  where
    type PredicateExp Prim = HardwarePrimType
    litE = sugarSymPrim . Lit
    varE = sugarSymPrim . FreeVar

instance EvaluateExp Prim
  where
    evalE = evalPrim

--------------------------------------------------------------------------------

instance (HardwarePrimType a, Num a) => Num (Prim a)
  where
    fromInteger = litE . fromInteger
    (+)         = sugarSymPrim Add
    (-)         = sugarSymPrim Sub
    (*)         = sugarSymPrim Mul
    negate      = sugarSymPrim Neg
    abs         = error "Num (Prim a): abs."
    signum      = error "Num (Prim a): signum."

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval HardwarePrim
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

instance Symbol HardwarePrim
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

instance Render HardwarePrim
  where
    renderSym  = show
    renderArgs = renderArgsSmart

instance Equality HardwarePrim
  where
    equal s1 s2 = show s1 == show s2

instance StringTree HardwarePrim
instance EvalEnv HardwarePrim env

--------------------------------------------------------------------------------
