{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Hardware.Primitive where

import Feldspar.Representation
import Data.Struct

import Data.Array ((!))
import Data.Bits (Bits)
import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable hiding (TypeRep)
import Data.Constraint hiding (Sub)
import qualified Data.Bits as Bits

-- syntactic.
import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

-- hardware-edsl.
import Language.Embedded.Hardware.Interface
import qualified Language.Embedded.Hardware.Expression.Represent.Bit as Imp (Bits)
import qualified Language.Embedded.Hardware.Expression.Frontend  as Imp
import qualified Language.Embedded.Hardware.Expression.Represent as Imp
import qualified Language.Embedded.Hardware.Command as Imp (IArray(..))

import GHC.TypeLits (KnownNat)

--------------------------------------------------------------------------------
-- * Hardware primitives.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * Hardware primitive types.

-- | Representation of supported, primitive software types.
data HardwarePrimTypeRep a
  where
    -- booleans
    BoolHT    :: HardwarePrimTypeRep Bool
    -- integers
    IntegerHT :: HardwarePrimTypeRep Integer
    -- signed numbers.
    Int8HT    :: HardwarePrimTypeRep Int8
    Int16HT   :: HardwarePrimTypeRep Int16
    Int32HT   :: HardwarePrimTypeRep Int32
    Int64HT   :: HardwarePrimTypeRep Int64
    -- unsigned numbers.
    Word8HT   :: HardwarePrimTypeRep Word8
    Word16HT  :: HardwarePrimTypeRep Word16
    Word32HT  :: HardwarePrimTypeRep Word32
    Word64HT  :: HardwarePrimTypeRep Word64
    -- bits.
    BitsHT    :: KnownNat n => HardwarePrimTypeRep (Imp.Bits n)

deriving instance Eq       (HardwarePrimTypeRep a)
deriving instance Show     (HardwarePrimTypeRep a)
deriving instance Typeable (HardwarePrimTypeRep a)

--------------------------------------------------------------------------------

-- | Class of supported, primitive hardware types.
class (Eq a, Show a, Typeable a, Inhabited a) => HardwarePrimType a
  where
    hardwareRep :: HardwarePrimTypeRep a

instance HardwarePrimType Bool    where hardwareRep = BoolHT
instance HardwarePrimType Integer where hardwareRep = IntegerHT
instance HardwarePrimType Int8    where hardwareRep = Int8HT
instance HardwarePrimType Int16   where hardwareRep = Int16HT
instance HardwarePrimType Int32   where hardwareRep = Int32HT
instance HardwarePrimType Int64   where hardwareRep = Int64HT
instance HardwarePrimType Word8   where hardwareRep = Word8HT
instance HardwarePrimType Word16  where hardwareRep = Word16HT
instance HardwarePrimType Word32  where hardwareRep = Word32HT
instance HardwarePrimType Word64  where hardwareRep = Word64HT

instance KnownNat n => HardwarePrimType (Imp.Bits n)
  where
    hardwareRep = BitsHT

-- | Compare two primitive hardware types for equality.
hardwarePrimTypeEq :: HardwarePrimTypeRep a -> HardwarePrimTypeRep b -> Maybe (Dict (a ~ b))
hardwarePrimTypeEq (BoolHT)    (BoolHT)    = Just Dict
hardwarePrimTypeEq (IntegerHT) (IntegerHT) = Just Dict
hardwarePrimTypeEq (Int8HT)    (Int8HT)    = Just Dict
hardwarePrimTypeEq (Int16HT)   (Int16HT)   = Just Dict
hardwarePrimTypeEq (Int32HT)   (Int32HT)   = Just Dict
hardwarePrimTypeEq (Int64HT)   (Int64HT)   = Just Dict
hardwarePrimTypeEq (Word8HT)   (Word8HT)   = Just Dict
hardwarePrimTypeEq (Word16HT)  (Word16HT)  = Just Dict
hardwarePrimTypeEq (Word32HT)  (Word32HT)  = Just Dict
hardwarePrimTypeEq (Word64HT)  (Word64HT)  = Just Dict
hardwarePrimTypeEq _           _           = Nothing

-- | Construct the primitive hardware type representation of 'a'.
hardwarePrimTypeOf :: HardwarePrimType a => a -> HardwarePrimTypeRep a
hardwarePrimTypeOf _ = hardwareRep

-- | Construct a primitive hardware type witness from its representation.
hardwarePrimWitType :: HardwarePrimTypeRep a -> Dict (HardwarePrimType a)
hardwarePrimWitType BoolHT    = Dict
hardwarePrimWitType IntegerHT = Dict
hardwarePrimWitType Int8HT    = Dict
hardwarePrimWitType Int16HT   = Dict
hardwarePrimWitType Int32HT   = Dict
hardwarePrimWitType Int64HT   = Dict
hardwarePrimWitType Word8HT   = Dict
hardwarePrimWitType Word16HT  = Dict
hardwarePrimWitType Word32HT  = Dict
hardwarePrimWitType Word64HT  = Dict
hardwarePrimWitType BitsHT    = Dict

--------------------------------------------------------------------------------
-- ** Hardware primitive expressions.

-- | Hardware primitive symbols.
data HardwarePrim sig
  where
    -- ^ free variables and literals.
    FreeVar :: (HardwarePrimType a) => String -> HardwarePrim (Full a)
    Lit     :: (Show a, Eq a)       => a      -> HardwarePrim (Full a)

    -- ^ type casting.
    Cast :: (HardwarePrimType a, HardwarePrimType b)
      => (a -> b) -> HardwarePrim (a :-> Full b)
    I2N :: (HardwarePrimType a, Integral a, HardwarePrimType b, Num b)
      => HardwarePrim (a :-> Full b)
    
    -- ^ conditional
    Cond :: HardwarePrim (Bool :-> a :-> a :-> Full a)
    
    -- ^ array indexing.
    ArrIx :: (HardwarePrimType a)
      => Imp.IArray a -> HardwarePrim (Integer :-> Full a)
            
    -- ^ numerical operations.
    Neg :: (HardwarePrimType a, Num a) => HardwarePrim (a :-> Full a)
    Add :: (HardwarePrimType a, Num a) => HardwarePrim (a :-> a :-> Full a)
    Sub :: (HardwarePrimType a, Num a) => HardwarePrim (a :-> a :-> Full a)
    Mul :: (HardwarePrimType a, Num a) => HardwarePrim (a :-> a :-> Full a)

    -- ^ integral operations.
    Div :: (HardwarePrimType a, Integral a) => HardwarePrim (a :-> a :-> Full a)
    Mod :: (HardwarePrimType a, Integral a) => HardwarePrim (a :-> a :-> Full a)

    -- ^ logical operations.
    Not :: HardwarePrim (Bool :-> Full Bool)
    And :: HardwarePrim (Bool :-> Bool :-> Full Bool)
    Or  :: HardwarePrim (Bool :-> Bool :-> Full Bool)

    -- ^ bitwise logical operations.
    BitAnd   :: (HardwarePrimType a, Bits a) => HardwarePrim (a :-> a :-> Full a)
    BitOr    :: (HardwarePrimType a, Bits a) => HardwarePrim (a :-> a :-> Full a)
    BitXor   :: (HardwarePrimType a, Bits a) => HardwarePrim (a :-> a :-> Full a)
    BitCompl :: (HardwarePrimType a, Bits a) => HardwarePrim (a :-> Full a)
    ShiftL   :: (HardwarePrimType a, Bits a, HardwarePrimType b, Integral b)
      => HardwarePrim (a :-> b :-> Full a)
    ShiftR   :: (HardwarePrimType a, Bits a, HardwarePrimType b, Integral b)
      => HardwarePrim (a :-> b :-> Full a)
    RotateL  :: (HardwarePrimType a, Bits a, HardwarePrimType b, Integral b)
      => HardwarePrim (a :-> b :-> Full a)
    RotateR  :: (HardwarePrimType a, Bits a, HardwarePrimType b, Integral b)
      => HardwarePrim (a :-> b :-> Full a)
    
    -- ^ relational operations.
    Eq  :: (HardwarePrimType a, Eq a)  => HardwarePrim (a :-> a :-> Full Bool)
    Lt  :: (HardwarePrimType a, Ord a) => HardwarePrim (a :-> a :-> Full Bool)
    Lte :: (HardwarePrimType a, Ord a) => HardwarePrim (a :-> a :-> Full Bool)
    Gt  :: (HardwarePrimType a, Ord a) => HardwarePrim (a :-> a :-> Full Bool)
    Gte :: (HardwarePrimType a, Ord a) => HardwarePrim (a :-> a :-> Full Bool)

deriving instance Show     (HardwarePrim a)
deriving instance Typeable (HardwarePrim a)

--------------------------------------------------------------------------------

-- | Hardware primitive symbols.
type HardwarePrimConstructs = HardwarePrim

-- | Hardware primitive symbols tagged with their type representation.
type HardwarePrimDomain = HardwarePrimConstructs :&: HardwarePrimTypeRep

-- | Hardware primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF HardwarePrimDomain a }

-- | Evaluate a closed, hardware primitive expression.
evalPrim :: Prim a -> a
evalPrim = go . unPrim
  where
    go :: AST HardwarePrimDomain sig -> Denotation sig
    go (Sym (s :&: _)) = evalSym s
    go (f :$ a)        = go f $ go a

-- | Sugar a hardware primitive symbol as a smart constructor.
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

instance Syntactic (Prim a)
  where
    type Domain   (Prim a) = HardwarePrimDomain
    type Internal (Prim a) = a
    desugar = unPrim
    sugar   = Prim

instance FreeExp Prim
  where
    type PredicateExp Prim = HardwarePrimType
    litE = sugarSymPrim . Lit
    varE = sugarSymPrim . FreeVar

instance EvaluateExp Prim
  where
    evalE = evalPrim

--------------------------------------------------------------------------------
-- front-end.

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
-- hardware expressions needed for 'compileAXI', I'll make them prettier later.

instance Imp.Expr Prim
  where
    true  = litE True
    false = litE False
    and   = sugarSymPrim And
    or    = sugarSymPrim Or
    xor   = error "todo: prim xor"
    xnor  = error "todo: prim xnor"
    nand  = error "todo: prim nand"
    nor   = error "todo: prim nor"

instance Imp.Rel Prim
  where
    eq (a :: Prim a) (b :: Prim a) =
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim Eq a b
    neq a b = Imp.not (Imp.eq a b)
    lt  (a :: Prim a) (b :: Prim a) =
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim Lt a b
    lte (a :: Prim a) (b :: Prim a) =
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim Lte a b
    gt  (a :: Prim a) (b :: Prim a) =
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim Gt a b
    gte (a :: Prim a) (b :: Prim a) =
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim Gte a b

instance Imp.Factor Prim
  where
    exp = error "todo: prim exp."
    abs = error "todo: prim abs."
    not = sugarSymPrim Not

instance Imp.Primary Prim
  where
    value (a :: a) = 
      case primDict (Imp.typeRep :: Imp.TypeRep a) of
        Dict -> sugarSymPrim (Lit a)
    name  = error "todo: prim name."
    cast (f :: a -> b) (a :: Prim a)  =
      case ( primDict (Imp.typeRep :: Imp.TypeRep a)
           , primDict (Imp.typeRep :: Imp.TypeRep b))
      of
        (Dict, Dict) -> sugarSymPrim (Cast f) a

primDict :: Imp.TypeRep a -> Dict (HardwarePrimType a)
primDict rep = case rep of
  Imp.BoolT    -> Dict
  Imp.Int8T    -> Dict
  Imp.Int16T   -> Dict
  Imp.Int32T   -> Dict
  Imp.Int64T   -> Dict
  Imp.Word8T   -> Dict
  Imp.Word16T  -> Dict
  Imp.Word32T  -> Dict
  Imp.Word64T  -> Dict
  Imp.IntegerT -> Dict
  Imp.BitsT    -> Dict
  _            -> error "todo: primDict."

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval HardwarePrim
  where
    evalSym (FreeVar v) = error $ "evaluating free variable " ++ show v
    evalSym (Lit a)     = a
    evalSym Cond        = \c t f -> if c then t else f
    evalSym Neg         = negate
    evalSym Add         = (+)
    evalSym Sub         = (-)
    evalSym Mul         = (*)
    evalSym Div         = div
    evalSym Mod         = mod
    evalSym (Cast f)    = f
    evalSym I2N         = fromIntegral
    evalSym Not         = not
    evalSym And         = (&&)
    evalSym Or          = (||)
    evalSym BitAnd      = (Bits..&.)
    evalSym BitOr       = (Bits..|.)
    evalSym BitXor      = Bits.xor
    evalSym BitCompl    = Bits.complement
    evalSym ShiftL      = \b i -> Bits.shiftL  b (fromIntegral i)
    evalSym ShiftR      = \b i -> Bits.shiftR  b (fromIntegral i)
    evalSym RotateL     = \b i -> Bits.rotateL b (fromIntegral i)
    evalSym RotateR     = \b i -> Bits.rotateR b (fromIntegral i)
    evalSym Eq          = (==)
    evalSym Lt          = (<)
    evalSym Lte         = (<=)
    evalSym Gt          = (>)
    evalSym Gte         = (>=)
    evalSym (ArrIx (Imp.IArrayE a)) = \i -> a ! toInteger i
    evalSym (ArrIx _)   = error "eval of array variable"

instance Symbol HardwarePrim
  where
    symSig (FreeVar v) = signature
    symSig (Lit a)     = signature
    symSig Cond        = signature
    symSig Neg         = signature
    symSig Add         = signature
    symSig Sub         = signature
    symSig Mul         = signature
    symSig Div         = signature
    symSig Mod         = signature
    symSig (Cast f)    = signature
    symSig I2N         = signature
    symSig Not         = signature
    symSig And         = signature
    symSig Or          = signature
    symSig BitAnd      = signature
    symSig BitOr       = signature
    symSig BitXor      = signature
    symSig BitCompl    = signature
    symSig ShiftL      = signature
    symSig ShiftR      = signature
    symSig RotateL     = signature
    symSig RotateR     = signature
    symSig Eq          = signature
    symSig Lt          = signature
    symSig Lte         = signature
    symSig Gt          = signature
    symSig Gte         = signature
    symSig (ArrIx a)   = signature

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
