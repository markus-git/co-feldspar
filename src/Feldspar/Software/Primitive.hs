{-# language GADTs                 #-}
{-# language StandaloneDeriving    #-}
{-# language TypeOperators         #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language UndecidableInstances  #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies          #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Software.Primitive where

import Feldspar.Representation
import Data.Struct

import Data.Array ((!))
import Data.Bits (Bits)
import Data.Complex
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
import qualified Language.Syntactic as Syn

-- imperative-edsl.
import Language.Embedded.Expression
import qualified Language.Embedded.Imperative.CMD as Imp (IArr(..))

--------------------------------------------------------------------------------
-- * Software primitives.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Software primitive types.

-- | Representation of supported, primitive software types.
data SoftwarePrimTypeRep a
  where
    -- booleans
    BoolST   :: SoftwarePrimTypeRep Bool
    -- signed numbers.
    Int8ST   :: SoftwarePrimTypeRep Int8
    Int16ST  :: SoftwarePrimTypeRep Int16
    Int32ST  :: SoftwarePrimTypeRep Int32
    Int64ST  :: SoftwarePrimTypeRep Int64
    -- unsigned numbers.
    Word8ST  :: SoftwarePrimTypeRep Word8
    Word16ST :: SoftwarePrimTypeRep Word16
    Word32ST :: SoftwarePrimTypeRep Word32
    Word64ST :: SoftwarePrimTypeRep Word64
    -- floating point numbers.
    FloatST  :: SoftwarePrimTypeRep Float
    DoubleST :: SoftwarePrimTypeRep Double
    -- complex numbers.
    ComplexFloatST  :: SoftwarePrimTypeRep (Complex Float)
    ComplexDoubleST :: SoftwarePrimTypeRep (Complex Double)

deriving instance Eq       (SoftwarePrimTypeRep a)
deriving instance Show     (SoftwarePrimTypeRep a)
deriving instance Typeable (SoftwarePrimTypeRep a)

instance Inhabited (Complex Float)
  where
    reset = 0 :+ 0

instance Inhabited (Complex Double)
  where
    reset = 0 :+ 0

--------------------------------------------------------------------------------

-- | Class of supported, primitive software types.
class (Eq a, Show a, Typeable a, Inhabited a) => SoftwarePrimType a
  where
    softwareRep :: SoftwarePrimTypeRep a

instance SoftwarePrimType Bool   where softwareRep = BoolST
instance SoftwarePrimType Int8   where softwareRep = Int8ST
instance SoftwarePrimType Int16  where softwareRep = Int16ST
instance SoftwarePrimType Int32  where softwareRep = Int32ST
instance SoftwarePrimType Int64  where softwareRep = Int64ST
instance SoftwarePrimType Word8  where softwareRep = Word8ST
instance SoftwarePrimType Word16 where softwareRep = Word16ST
instance SoftwarePrimType Word32 where softwareRep = Word32ST
instance SoftwarePrimType Word64 where softwareRep = Word64ST
instance SoftwarePrimType Float  where softwareRep = FloatST
instance SoftwarePrimType Double where softwareRep = DoubleST
instance SoftwarePrimType (Complex Float)  where softwareRep = ComplexFloatST
instance SoftwarePrimType (Complex Double) where softwareRep = ComplexDoubleST

-- | Compare two primitive software types for equality.
softwarePrimTypeEq :: SoftwarePrimTypeRep a -> SoftwarePrimTypeRep b -> Maybe (Dict (a ~ b))
softwarePrimTypeEq (BoolST)   (BoolST)   = Just Dict
softwarePrimTypeEq (Int8ST)   (Int8ST)   = Just Dict
softwarePrimTypeEq (Int16ST)  (Int16ST)  = Just Dict
softwarePrimTypeEq (Int32ST)  (Int32ST)  = Just Dict
softwarePrimTypeEq (Int64ST)  (Int64ST)  = Just Dict
softwarePrimTypeEq (Word8ST)  (Word8ST)  = Just Dict
softwarePrimTypeEq (Word16ST) (Word16ST) = Just Dict
softwarePrimTypeEq (Word32ST) (Word32ST) = Just Dict
softwarePrimTypeEq (Word64ST) (Word64ST) = Just Dict
softwarePrimTypeEq (FloatST)  (FloatST)  = Just Dict
softwarePrimTypeEq (DoubleST) (DoubleST) = Just Dict
softwarePrimTypeEq (ComplexFloatST)  (ComplexFloatST)  = Just Dict
softwarePrimTypeEq (ComplexDoubleST) (ComplexDoubleST) = Just Dict
softwarePrimTypeEq _          _          = Nothing

-- | Construct the primitive software type representation of 'a'.
softwarePrimTypeOf :: SoftwarePrimType a => a -> SoftwarePrimTypeRep a
softwarePrimTypeOf _ = softwareRep

-- | Construct a primitive software type witness from its representation.
softwarePrimWitType :: SoftwarePrimTypeRep a -> Dict (SoftwarePrimType a)
softwarePrimWitType BoolST   = Dict
softwarePrimWitType Int8ST   = Dict
softwarePrimWitType Int16ST  = Dict
softwarePrimWitType Int32ST  = Dict
softwarePrimWitType Int64ST  = Dict
softwarePrimWitType Word8ST  = Dict
softwarePrimWitType Word16ST = Dict
softwarePrimWitType Word32ST = Dict
softwarePrimWitType Word64ST = Dict
softwarePrimWitType FloatST  = Dict
softwarePrimWitType DoubleST = Dict
softwarePrimWitType ComplexFloatST  = Dict
softwarePrimWitType ComplexDoubleST = Dict

--------------------------------------------------------------------------------
-- ** Software primitive expressions.

-- | Software primitive symbols.
data SoftwarePrim sig
  where
    -- free variables and literals.
    FreeVar :: (SoftwarePrimType a) => String -> SoftwarePrim (Full a)
    Lit     :: (Show a, Eq a)       => a      -> SoftwarePrim (Full a)
    -- numerical operations.
    Neg  :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> Full a)
    Abs  :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> Full a)
    Sign :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> Full a)
    Add  :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> a :-> Full a)
    Sub  :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> a :-> Full a)
    Mul  :: (SoftwarePrimType a, Num a) => SoftwarePrim (a :-> a :-> Full a)
    -- integral operations.
    Div  :: (SoftwarePrimType a, Integral a) => SoftwarePrim (a :-> a :-> Full a)
    Mod  :: (SoftwarePrimType a, Integral a) => SoftwarePrim (a :-> a :-> Full a)
    Quot :: (SoftwarePrimType a, Integral a) => SoftwarePrim (a :-> a :-> Full a)
    Rem  :: (SoftwarePrimType a, Integral a) => SoftwarePrim (a :-> a :-> Full a)
    --
    FDiv :: (SoftwarePrimType a, Fractional a) => SoftwarePrim (a :-> a :-> Full a)
    -- floating point operators.
    Pi    :: (SoftwarePrimType a, Floating a) => SoftwarePrim (Full a)
    Exp   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Log   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Sqrt  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Pow   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> a :-> Full a)
    Sin   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Cos   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Tan   :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Asin  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Acos  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Atan  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Sinh  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Cosh  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Tanh  :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Asinh :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Acosh :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    Atanh :: (SoftwarePrimType a, Floating a) => SoftwarePrim (a :-> Full a)
    -- complex operators.
    Complex   :: (SoftwarePrimType a, SoftwarePrimType (Complex a), Num a) =>
      SoftwarePrim (a :-> a :-> Full (Complex a))
    Real      :: (SoftwarePrimType a, SoftwarePrimType (Complex a)) =>
      SoftwarePrim (Complex a :-> Full a)
    Imag      :: (SoftwarePrimType a, SoftwarePrimType (Complex a)) =>
      SoftwarePrim (Complex a :-> Full a)
    Polar     :: (SoftwarePrimType a, SoftwarePrimType (Complex a), Floating a) =>
      SoftwarePrim (a :-> a :-> Full (Complex a))
    Magnitude :: (SoftwarePrimType a, SoftwarePrimType (Complex a), RealFloat a) =>
      SoftwarePrim (Complex a :-> Full a)
    Phase     :: (SoftwarePrimType a, SoftwarePrimType (Complex a), RealFloat a) =>
      SoftwarePrim (Complex a :-> Full a)
    Conjugate :: (SoftwarePrimType a, SoftwarePrimType (Complex a), Num a) =>
      SoftwarePrim (Complex a :-> Full (Complex a))
    -- type casting.
    I2N   :: (SoftwarePrimType a, Integral a, SoftwarePrimType b, Num b) =>
      SoftwarePrim (a :-> Full b)
    I2B   :: (SoftwarePrimType a, Integral a) =>
      SoftwarePrim (a :-> Full Bool)
    B2I   :: (SoftwarePrimType a, Integral a) =>
      SoftwarePrim (Bool :-> Full a)
    Round :: (SoftwarePrimType a, RealFrac a, SoftwarePrimType b, Num b) =>
      SoftwarePrim (a :-> Full b)
    -- logical operations.
    Not     :: SoftwarePrim (Bool :-> Full Bool)
    And     :: SoftwarePrim (Bool :-> Bool :-> Full Bool)
    Or      :: SoftwarePrim (Bool :-> Bool :-> Full Bool)
    -- bitwise logical operations.
    BitAnd   :: (SoftwarePrimType a, Bits a) => SoftwarePrim (a :-> a :-> Full a)
    BitOr    :: (SoftwarePrimType a, Bits a) => SoftwarePrim (a :-> a :-> Full a)
    BitXor   :: (SoftwarePrimType a, Bits a) => SoftwarePrim (a :-> a :-> Full a)
    BitCompl :: (SoftwarePrimType a, Bits a) => SoftwarePrim (a :-> Full a)
    ShiftL   :: (SoftwarePrimType a, Bits a, SoftwarePrimType b, Integral b) =>
      SoftwarePrim (a :-> b :-> Full a)
    ShiftR   :: (SoftwarePrimType a, Bits a, SoftwarePrimType b, Integral b) =>
      SoftwarePrim (a :-> b :-> Full a)
    RotateL  :: (SoftwarePrimType a, Bits a, SoftwarePrimType b, Integral b) =>
      SoftwarePrim (a :-> b :-> Full a)
    RotateR  :: (SoftwarePrimType a, Bits a, SoftwarePrimType b, Integral b) =>
      SoftwarePrim (a :-> b :-> Full a)
    -- relational operations.
    Eq  :: (SoftwarePrimType a, Eq a)  => SoftwarePrim (a :-> a :-> Full Bool)
    Neq :: (SoftwarePrimType a, Eq a)  => SoftwarePrim (a :-> a :-> Full Bool)
    Lt  :: (SoftwarePrimType a, Ord a) => SoftwarePrim (a :-> a :-> Full Bool)
    Lte :: (SoftwarePrimType a, Ord a) => SoftwarePrim (a :-> a :-> Full Bool)
    Gt  :: (SoftwarePrimType a, Ord a) => SoftwarePrim (a :-> a :-> Full Bool)
    Gte :: (SoftwarePrimType a, Ord a) => SoftwarePrim (a :-> a :-> Full Bool)
    -- conditional.
    Cond :: SoftwarePrim (Bool :-> a :-> a :-> Full a)
    -- array indexing.
    ArrIx :: (SoftwarePrimType a) => Imp.IArr Index a ->
      SoftwarePrim (Index :-> Full a)

deriving instance Show     (SoftwarePrim a)
deriving instance Typeable (SoftwarePrim a)

--------------------------------------------------------------------------------

-- | Software primitive symbols.
type SoftwarePrimConstructs = SoftwarePrim

-- | Software primitive symbols tagged with their type representation.
type SoftwarePrimDomain = SoftwarePrimConstructs :&: SoftwarePrimTypeRep

-- | Software primitive expressions.
newtype Prim a = Prim { unPrim :: ASTF SoftwarePrimDomain a }

-- | Evaluate a closed, software primitive expression.
evalPrim :: Prim a -> a
evalPrim = go . unPrim
  where
    go :: AST SoftwarePrimDomain sig -> Denotation sig
    go (Sym (s :&: _)) = evalSym s
    go (f :$ a)        = go f $ go a

-- | Sugar a software primitive symbol as a smart constructor.
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

instance Syntactic (Prim a)
  where
    type Domain   (Prim a) = SoftwarePrimDomain
    type Internal (Prim a) = a
    desugar = unPrim
    sugar   = Prim

instance FreeExp Prim
  where
    type FreePred Prim = SoftwarePrimType
    constExp = sugarSymPrim . Lit
    varExp   = sugarSymPrim . FreeVar

instance EvalExp Prim
  where
    evalExp = evalPrim

--------------------------------------------------------------------------------
-- front-end.

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
    evalSym Cond        = \c t f -> if c then t else f
    evalSym Neg         = negate
    evalSym Abs         = abs
    evalSym Sign        = signum
    evalSym Add         = (+)
    evalSym Sub         = (-)
    evalSym Mul         = (*)
    evalSym Div         = div
    evalSym Mod         = mod
    evalSym Quot        = quot
    evalSym Rem         = rem
    evalSym FDiv        = (/)
    evalSym Pi          = pi
    evalSym Exp         = exp
    evalSym Log         = log
    evalSym Sqrt        = sqrt
    evalSym Pow         = (**)
    evalSym Sin         = sin
    evalSym Cos         = cos
    evalSym Tan         = tan
    evalSym Asin        = asin
    evalSym Acos        = acos
    evalSym Atan        = atan
    evalSym Sinh        = sinh
    evalSym Cosh        = cosh
    evalSym Tanh        = tanh
    evalSym Asinh       = asinh
    evalSym Acosh       = acosh
    evalSym Atanh       = atanh
    evalSym Complex     = (:+)
    evalSym Polar       = mkPolar
    evalSym Real        = realPart
    evalSym Imag        = imagPart
    evalSym Magnitude   = magnitude
    evalSym Phase       = phase
    evalSym Conjugate   = conjugate
    evalSym I2N         = fromIntegral
    evalSym I2B         = (/=0)
    evalSym B2I         = \a -> if a then 1 else 0
    evalSym Round       = fromInteger . round
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
    evalSym Neq         = (/=)
    evalSym Lt          = (<)
    evalSym Lte         = (<=)
    evalSym Gt          = (>)
    evalSym Gte         = (>=)
    evalSym (ArrIx (Imp.IArrRun arr)) = \i -> arr ! i
    evalSym (ArrIx _)   = error "eval of variable."

instance Symbol SoftwarePrim
  where
    symSig (FreeVar v) = signature
    symSig (Lit a)     = signature
    symSig Cond        = signature
    symSig Neg         = signature
    symSig Abs         = signature
    symSig Sign        = signature
    symSig Add         = signature
    symSig Sub         = signature
    symSig Mul         = signature
    symSig Div         = signature
    symSig Mod         = signature
    symSig Quot        = signature
    symSig Rem         = signature
    symSig FDiv        = signature
    symSig Pi          = signature
    symSig Exp         = signature
    symSig Log         = signature
    symSig Sqrt        = signature
    symSig Pow         = signature
    symSig Sin         = signature
    symSig Cos         = signature
    symSig Tan         = signature
    symSig Asin        = signature
    symSig Acos        = signature
    symSig Atan        = signature
    symSig Sinh        = signature
    symSig Cosh        = signature
    symSig Tanh        = signature
    symSig Asinh       = signature
    symSig Acosh       = signature
    symSig Atanh       = signature
    symSig Complex     = signature
    symSig Real        = signature
    symSig Imag        = signature
    symSig Polar       = signature
    symSig Magnitude   = signature
    symSig Phase       = signature
    symSig Conjugate   = signature
    symSig I2N         = signature
    symSig I2B         = signature
    symSig B2I         = signature
    symSig Round       = signature
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
    symSig Neq         = signature
    symSig Lt          = signature
    symSig Lte         = signature
    symSig Gt          = signature
    symSig Gte         = signature
    symSig (ArrIx a)   = signature

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
