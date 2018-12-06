{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}
{-# language DataKinds #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language GeneralizedNewtypeDeriving #-}

module Feldspar.Software.Verify.Primitive where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Representation hiding (Nil)
import Feldspar.Software.Verify.Command
import Feldspar.Verify.Arithmetic

import Data.Struct

import qualified Control.Monad.FirstOrder as FO
import qualified SimpleSMT as SMT hiding (not, declareFun)

import Feldspar.Verify.Monad (Verify)
import qualified Feldspar.Verify.Monad    as V
import qualified Feldspar.Verify.SMT      as SMT
import qualified Feldspar.Verify.Abstract as A
import qualified Data.Map.Strict          as Map
import qualified Control.Monad.RWS.Strict as S

import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

import qualified Data.Bits as Bits
import qualified Data.Complex as Complex
import Data.Constraint hiding (Sub)
import Data.Int
import Data.Word
import Data.Typeable

import Language.Syntactic

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

newtype Symbolic a = Symbolic { unSymbolic :: Rat }
  deriving (Eq, Ord, Show, V.TypedSExpr, V.SMTOrd)

instance V.Fresh (Symbolic a)
  where
    fresh = V.freshSExpr

symbCast :: Symbolic a -> Symbolic b
symbCast = Symbolic . unSymbolic

symbFun :: SymbParam a => String -> [Symbolic a] -> Symbolic a
symbFun name (args :: [Symbolic a]) = V.fromSMT $
  SMT.fun (symbType (undefined :: a) ++ "-" ++ name) (map V.toSMT args)

fromComplexConstant :: (RealFrac a, SymbParam b) => Complex.Complex a -> Symbolic b
fromComplexConstant c = symbFun "complex" [real, imag]
  where
    real = Symbolic $ fromRational $ toRational $ Complex.realPart c
    imag = Symbolic $ fromRational $ toRational $ Complex.imagPart c

--------------------------------------------------------------------------------

data SymbFloat
data SymbDouble
data SymbComplexFloat
data SymbComplexDouble

class SymbParam a
  where
    symbType :: a -> String

instance SymbParam SymbFloat  where symbType _ = "float"
instance SymbParam SymbDouble where symbType _ = "double"
instance SymbParam SymbComplexFloat  where symbType _ = "cfloat"
instance SymbParam SymbComplexDouble where symbType _ = "cdouble"

instance SymbParam a => Num (Symbolic a)
  where
    fromInteger = Symbolic . fromInteger
    x + y  = symbFun "+" [x, y]
    x - y  = symbFun "-" [x, y]
    x * y  = symbFun "*" [x, y]
    abs    = smtAbs
    signum = smtSignum

instance SymbParam a => Fractional (Symbolic a) where
  fromRational = Symbolic . fromRational
  x / y = symbFun "/" [x, y]

instance SymbParam a => Floating (Symbolic a) where
  pi      = fromRational (toRational pi)
  exp x   = symbFun "exp" [x]
  log x   = symbFun "log" [x]
  sqrt x  = symbFun "sqrt" [x]
  x ** y  = symbFun "pow" [x, y]
  sin x   = symbFun "sin" [x]
  cos x   = symbFun "cos" [x]
  tan x   = symbFun "tan" [x]
  asin x  = symbFun "asin" [x]
  acos x  = symbFun "acos" [x]
  atan x  = symbFun "atan" [x]
  sinh x  = symbFun "sinh" [x]
  cosh x  = symbFun "cosh" [x]
  tanh x  = symbFun "tanh" [x]
  asinh x = symbFun "asinh" [x]
  acosh x = symbFun "acosh" [x]
  atanh x = symbFun "atanh" [x]

--------------------------------------------------------------------------------

class Floating a => Complex a
  where
    type RealPart a
    complex   :: RealPart a -> RealPart a -> a
    polar     :: RealPart a -> RealPart a -> a
    real      :: a -> RealPart a
    imag      :: a -> RealPart a
    magnitude :: a -> RealPart a
    phase     :: a -> RealPart a
    conjugate :: a -> a

instance Complex (V.SMTExpr Prim (Complex.Complex Float))
  where
    type RealPart (V.SMTExpr Prim (Complex.Complex Float)) = V.SMTExpr Prim Float
    complex   (Float x) (Float y) = ComplexFloat (complex x y)
    polar     (Float x) (Float y) = ComplexFloat (polar x y)
    real      (ComplexFloat x)    = Float (real x)
    imag      (ComplexFloat x)    = Float (imag x)
    magnitude (ComplexFloat x)    = Float (magnitude x)
    phase     (ComplexFloat x)    = Float (phase x)
    conjugate (ComplexFloat x)    = ComplexFloat (conjugate x)

instance Complex (V.SMTExpr Prim (Complex.Complex Double))
  where
    type RealPart (V.SMTExpr Prim (Complex.Complex Double)) = V.SMTExpr Prim Double
    complex   (Double x) (Double y) = ComplexDouble (complex x y)
    polar     (Double x) (Double y) = ComplexDouble (polar x y)
    real      (ComplexDouble x)     = Double (real x)
    imag      (ComplexDouble x)     = Double (imag x)
    magnitude (ComplexDouble x)     = Double (magnitude x)
    phase     (ComplexDouble x)     = Double (phase x)
    conjugate (ComplexDouble x)     = ComplexDouble (conjugate x)

witnessComplex :: (SoftwarePrimType a, SoftwarePrimType (Complex.Complex a)) =>
  Prim (Complex.Complex a) ->
  Dict ( Floating (V.SMTExpr Prim a)
       , Complex  (V.SMTExpr Prim (Complex.Complex a))
       , RealPart (V.SMTExpr Prim (Complex.Complex a)) ~ V.SMTExpr Prim a)
witnessComplex (_ :: Prim (Complex.Complex a)) =
  case softwareRep :: SoftwarePrimTypeRep (Complex.Complex a) of
    ComplexFloatST  -> Dict
    ComplexDoubleST -> Dict

witnessFractional :: (SoftwarePrimType a, Fractional a) =>
  Prim a ->
  Dict (Floating (V.SMTExpr Prim a))
witnessFractional (_ :: Prim a) = case softwareRep :: SoftwarePrimTypeRep a of
    FloatST         -> Dict
    DoubleST        -> Dict
    ComplexFloatST  -> Dict
    ComplexDoubleST -> Dict

witnessIntegral :: (SoftwarePrimType a, Integral a) =>
  Prim a ->
  Dict ( Integral (V.SMTExpr Prim a)
       , Bits (V.SMTExpr Prim a))
witnessIntegral (_ :: Prim a) = case softwareRep :: SoftwarePrimTypeRep a of
  Int8ST   -> Dict
  Int16ST  -> Dict
  Int32ST  -> Dict
  Int64ST  -> Dict
  Word8ST  -> Dict
  Word16ST -> Dict
  Word32ST -> Dict
  Word64ST -> Dict

witnessBits :: (SoftwarePrimType a, Bits.Bits a) =>
  Prim a ->
  Dict ( Num a
       , Integral (V.SMTExpr Prim a)
       , Bits (V.SMTExpr Prim a))
witnessBits (_ :: Prim a) = case softwareRep :: SoftwarePrimTypeRep a of
  Int8ST   -> Dict
  Int16ST  -> Dict
  Int32ST  -> Dict
  Int64ST  -> Dict
  Word8ST  -> Dict
  Word16ST -> Dict
  Word32ST -> Dict
  Word64ST -> Dict

--------------------------------------------------------------------------------

toRat :: (SoftwarePrimType a, Fractional a) => V.SMTExpr Prim a -> Rat
toRat (x :: V.SMTExpr Prim a) = case softwareRep :: SoftwarePrimTypeRep a of
  FloatST         -> let Float         (Symbolic y) = x in y
  DoubleST        -> let Double        (Symbolic y) = x in y
  ComplexFloatST  -> let ComplexFloat  (Symbolic y) = x in y
  ComplexDoubleST -> let ComplexDouble (Symbolic y) = x in y

fromRat :: forall a. (SoftwarePrimType a, Num a) => Rat -> V.SMTExpr Prim a
fromRat x = case softwareRep :: SoftwarePrimTypeRep a of Int8ST -> Int8 (f2i x)
  where
    f2i :: forall s w. (Sign s, Width w) => Rat -> BV s w
    f2i (Rat x) = BV $ SMT.List [SMT.fam "int2bv" [width (undefined :: w)], SMT.fun "to_int" [x]]

i2n :: forall a b.
  ( V.SMTEval Prim a, SoftwarePrimType a, Integral a
  , V.SMTEval Prim b, SoftwarePrimType b, Num b) =>
  V.SMTExpr Prim a ->
  V.SMTExpr Prim b
i2n x = toBV x $ case softwareRep :: SoftwarePrimTypeRep b of
  Int8ST   -> Int8   . i2i
  Int16ST  -> Int16  . i2i
  Int32ST  -> Int32  . i2i
  Int64ST  -> Int64  . i2i
  Word8ST  -> Word8  . i2i
  Word16ST -> Word16 . i2i
  Word32ST -> Word32 . i2i
  Word64ST -> Word64 . i2i
  FloatST  -> Float  . Symbolic . i2f
  DoubleST -> Double . Symbolic . i2f
  ComplexFloatST  -> ComplexFloat  . Symbolic . i2f
  ComplexDoubleST -> ComplexDouble . Symbolic . i2f
  where
    toBV :: forall a b. (V.SMTEval Prim a, SoftwarePrimType a, Integral a) =>
      V.SMTExpr Prim a -> (forall s w. (Sign s, Width w) => BV s w -> b) -> b
    toBV (x :: V.SMTExpr Prim a) k = case softwareRep :: SoftwarePrimTypeRep a of
      Int8ST   -> let Int8   y = x in k y
      Int16ST  -> let Int16  y = x in k y
      Int32ST  -> let Int32  y = x in k y
      Int64ST  -> let Int64  y = x in k y
      Word8ST  -> let Word8  y = x in k y
      Word16ST -> let Word16 y = x in k y
      Word32ST -> let Word32 y = x in k y
      Word64ST -> let Word64 y = x in k y

    i2f :: (Sign s, Width w) => BV s w -> Rat
    i2f (BV x) = Rat (SMT.fun "to_real" [SMT.fun "bv2int" [x]])

    i2i :: forall s1 w1 s2 w2. (Sign s1, Width w1, Sign s2, Width w2) => BV s1 w1 -> BV s2 w2
    i2i x = case compare m n of
      LT | isSigned x -> V.fromSMT (SMT.signExtend (n-m) (V.toSMT x))
         | otherwise  -> V.fromSMT (SMT.zeroExtend (n-m) (V.toSMT x))
      EQ -> V.fromSMT (V.toSMT x)
      GT -> V.fromSMT (SMT.extract (V.toSMT x) (n-1) 0)
      where
        m = width (undefined :: w1)
        n = width (undefined :: w2)

--------------------------------------------------------------------------------

class SymbParam a => SymbComplex a
  where
    type SymbRealPart a

instance SymbComplex SymbComplexFloat
  where
    type SymbRealPart SymbComplexFloat  = SymbFloat

instance SymbComplex SymbComplexDouble
  where
    type SymbRealPart SymbComplexDouble = SymbDouble

instance SymbComplex a => Complex (Symbolic a)
  where
    type RealPart (Symbolic a) = Symbolic (SymbRealPart a)
    complex x y = symbFun "complex" [symbCast x, symbCast y]
    polar x y   = symbFun "polar" [symbCast x, symbCast y]
    real x      = symbCast (symbFun "real" [x])
    imag x      = symbCast (symbFun "imag" [x])
    magnitude x = symbCast (symbFun "magnitude" [x])
    phase x     = symbCast (symbFun "phase" [x])
    conjugate x = symbFun "conjugate" [x]

--------------------------------------------------------------------------------

declareSymbFun :: SymbParam a => String -> a ->
  [SMT.SExpr] -> SMT.SExpr -> SMT.SMT ()
declareSymbFun name (_ :: a) args res =
  S.void $ SMT.declareFun (symbType (undefined :: a) ++ "-" ++ name) args res

declareSymbArith :: SymbParam a => a -> SMT.SMT ()
declareSymbArith x = do
  declareSymbFun "+" x     [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "-" x     [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "*" x     [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "/" x     [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "exp" x   [SMT.tReal] SMT.tReal
  declareSymbFun "log" x   [SMT.tReal] SMT.tReal
  declareSymbFun "sqrt" x  [SMT.tReal] SMT.tReal
  declareSymbFun "pow" x   [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "sin" x   [SMT.tReal] SMT.tReal
  declareSymbFun "cos" x   [SMT.tReal] SMT.tReal
  declareSymbFun "tan" x   [SMT.tReal] SMT.tReal
  declareSymbFun "asin" x  [SMT.tReal] SMT.tReal
  declareSymbFun "acos" x  [SMT.tReal] SMT.tReal
  declareSymbFun "atan" x  [SMT.tReal] SMT.tReal
  declareSymbFun "sinh" x  [SMT.tReal] SMT.tReal
  declareSymbFun "cosh" x  [SMT.tReal] SMT.tReal
  declareSymbFun "tanh" x  [SMT.tReal] SMT.tReal
  declareSymbFun "asinh" x [SMT.tReal] SMT.tReal
  declareSymbFun "acosh" x [SMT.tReal] SMT.tReal
  declareSymbFun "atanh" x [SMT.tReal] SMT.tReal

declareSymbComplex :: SymbParam a => a -> SMT.SMT ()
declareSymbComplex x = do
  declareSymbArith x
  declareSymbFun "complex" x   [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "polar" x     [SMT.tReal, SMT.tReal] SMT.tReal
  declareSymbFun "real" x      [SMT.tReal] SMT.tReal
  declareSymbFun "imag" x      [SMT.tReal] SMT.tReal
  declareSymbFun "magnitude" x [SMT.tReal] SMT.tReal
  declareSymbFun "phase" x     [SMT.tReal] SMT.tReal
  declareSymbFun "conjugate" x [SMT.tReal] SMT.tReal

declareFeldsparGlobals :: SMT.SMT ()
declareFeldsparGlobals = do
  declareSymbArith   (undefined :: SymbFloat)
  declareSymbArith   (undefined :: SymbDouble)
  declareSymbComplex (undefined :: SymbComplexFloat)
  declareSymbComplex (undefined :: SymbComplexDouble)
  SMT.declareFun "skolem-int8"   [] (SMT.tBits 8)
  SMT.declareFun "skolem-int16"  [] (SMT.tBits 16)
  SMT.declareFun "skolem-int32"  [] (SMT.tBits 32)
  SMT.declareFun "skolem-int64"  [] (SMT.tBits 64)
  SMT.declareFun "skolem-word8"  [] (SMT.tBits 8)
  SMT.declareFun "skolem-word16" [] (SMT.tBits 16)
  SMT.declareFun "skolem-word32" [] (SMT.tBits 32)
  SMT.declareFun "skolem-word64" [] (SMT.tBits 64)
  return ()

instance FO.Substitute Prim
  where
    type SubstPred Prim = SoftwarePrimType
    subst sub (Prim exp) = Prim (everywhereUp f exp)
      where
        f :: ASTF SoftwarePrimDomain a -> ASTF SoftwarePrimDomain a
        f (Sym (FreeVar x :&: ty)) = case FO.lookupSubst sub (Imp.ValComp x) of
          Imp.ValComp y -> Sym (FreeVar y :&: ty)
          Imp.ValRun  z -> Sym (Lit z :&: ty)
        f (Sym (ArrIx iarr :&: ty) :$ i) = Sym (ArrIx iarr' :&: ty) :$ i
          where iarr' = FO.lookupSubst sub iarr
        f x = x

instance FO.TypeablePred SoftwarePrimType
  where
    witnessTypeable Dict = Dict

--------------------------------------------------------------------------------

instance V.SMTEval Prim Bool where
  fromConstant = Bool . SMT.bool
  witnessOrd _ = Dict

instance V.SMTEval Prim Int8 where
  fromConstant = Int8 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-int8" [])

instance V.SMTEval Prim Int16 where
  fromConstant = Int16 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-int16" [])

instance V.SMTEval Prim Int32 where
  fromConstant = Int32 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-int32" [])

instance V.SMTEval Prim Int64 where
  fromConstant = Int64 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-int64" [])

instance V.SMTEval Prim Word8 where
  fromConstant = Word8 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-word8" [])

instance V.SMTEval Prim Word16 where
  fromConstant = Word16 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-word16" [])

instance V.SMTEval Prim Word32 where
  fromConstant = Word32 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-word32" [])

instance V.SMTEval Prim Word64 where
  fromConstant = Word64 . fromIntegral
  witnessNum _ = Dict
  witnessOrd _ = Dict
  skolemIndex  = V.fromSMT (SMT.fun "skolem-word64" [])

instance V.SMTEval Prim Float where
  fromConstant = Float . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance V.SMTEval Prim Double where
  fromConstant = Double . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance V.SMTEval Prim (Complex.Complex Float) where
  fromConstant = ComplexFloat . fromComplexConstant
  witnessNum _ = Dict

instance V.SMTEval Prim (Complex.Complex Double) where
  fromConstant = ComplexDouble . fromComplexConstant
  witnessNum _ = Dict

--------------------------------------------------------------------------------

instance V.SMTEval1 Prim where
  type Pred Prim = SoftwarePrimType
  newtype SMTExpr Prim Bool   = Bool SMT.SExpr
    deriving (Typeable)
  newtype SMTExpr Prim Float  = Float  (Symbolic SymbFloat)
    deriving (Typeable, Num, Fractional, Floating, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Double = Double (Symbolic SymbDouble)
    deriving (Typeable, Num, Fractional, Floating, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim (Complex.Complex Float) =
      ComplexFloat (Symbolic SymbComplexFloat)
    deriving (Typeable, Num, Fractional, Floating, V.TypedSExpr)
  newtype SMTExpr Prim (Complex.Complex Double) =
      ComplexDouble (Symbolic SymbComplexDouble)
    deriving (Typeable, Num, Fractional, Floating, V.TypedSExpr)
  newtype SMTExpr Prim Int8   = Int8   (BV Signed W8)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Int16  = Int16  (BV Signed W16)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Int32  = Int32  (BV Signed W32)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Int64  = Int64  (BV Signed W64)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Word8  = Word8  (BV Unsigned W8)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Word16 = Word16 (BV Unsigned W16)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Word32 = Word32 (BV Unsigned W32)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)
  newtype SMTExpr Prim Word64 = Word64 (BV Unsigned W64)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, V.SMTOrd, V.TypedSExpr)

  eval (Prim exp :: Prim a) =
    simpleMatch (\(exp :&: ty) -> case softwarePrimWitType ty of
      Dict -> case V.witnessPred (undefined :: Prim a) of
        Dict -> verifyPrim exp) exp

  witnessPred (_ :: Prim a) = case softwareRep :: SoftwarePrimTypeRep a of
    BoolST   -> Dict
    Int8ST   -> Dict
    Int16ST  -> Dict
    Int32ST  -> Dict
    Int64ST  -> Dict
    Word8ST  -> Dict
    Word16ST -> Dict
    Word32ST -> Dict
    Word64ST -> Dict
    FloatST  -> Dict
    DoubleST -> Dict
    ComplexFloatST  -> Dict
    ComplexDoubleST -> Dict

instance V.SMTOrd (V.SMTExpr Prim Bool) where
  Bool x .<.  Bool y = SMT.not x SMT..&&. y
  Bool x .>.  Bool y = x SMT..&&. SMT.not y
  Bool x .<=. Bool y = SMT.not x SMT..||. y
  Bool x .>=. Bool y = x SMT..||. SMT.not y

instance V.TypedSExpr (V.SMTExpr Prim Bool) where
  smtType _ = SMT.tBool
  toSMT (Bool x) = x
  fromSMT x = Bool x

--------------------------------------------------------------------------------

verifyPrim :: forall a .
  (SoftwarePrimType (DenResult a), V.SMTEval Prim (DenResult a)) =>
  SoftwarePrim a ->
  Args (AST SoftwarePrimDomain) a ->
  V.Verify (V.SMTExpr Prim (DenResult a))
verifyPrim (FreeVar x) _ = peekValue x
verifyPrim (Lit x) _     = return (V.fromConstant x)
verifyPrim Add (x :* y :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    S.liftM2 (+) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Sub (x :* y :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    S.liftM2 (-) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Mul (x :* y :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    S.liftM2 (*) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Neg (x :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    fmap negate (V.eval (Prim x))
verifyPrim Abs (x :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    fmap abs (V.eval (Prim x))
verifyPrim Sign (x :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) =
    fmap signum (V.eval (Prim x))
verifyPrim Div (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    S.liftM2 div (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Mod (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    S.liftM2 mod (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Quot (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    S.liftM2 quot (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Rem (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    S.liftM2 rem (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim FDiv (x :* y :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    S.liftM2 (/) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Pi Nil
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    return pi
verifyPrim Exp (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap exp (V.eval (Prim x))
verifyPrim Log (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap log (V.eval (Prim x))
verifyPrim Sqrt (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sqrt (V.eval (Prim x))
verifyPrim Pow (x :* y :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    S.liftM2 (**) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Sin (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sin (V.eval (Prim x))
verifyPrim Cos (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap cos (V.eval (Prim x))
verifyPrim Tan (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap tan (V.eval (Prim x))
verifyPrim Asin (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap asin (V.eval (Prim x))
verifyPrim Acos (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap acos (V.eval (Prim x))
verifyPrim Atan (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap atan (V.eval (Prim x))
verifyPrim Sinh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sinh (V.eval (Prim x))
verifyPrim Cosh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap cosh (V.eval (Prim x))
verifyPrim Tanh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap tanh (V.eval (Prim x))
verifyPrim Asinh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap asinh (V.eval (Prim x))
verifyPrim Acosh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap acosh (V.eval (Prim x))
verifyPrim Atanh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap atanh (V.eval (Prim x))
verifyPrim Complex (x :* y :* Nil)
  | Dict <- witnessComplex (undefined :: Prim (DenResult a)) =
    S.liftM2 complex (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Polar (x :* y :* Nil)
  | Dict <- witnessComplex (undefined :: Prim (DenResult a)) =
    S.liftM2 polar (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim Real ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap real (V.eval (Prim x))
verifyPrim Imag ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap imag (V.eval (Prim x))
verifyPrim Magnitude ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap magnitude (V.eval (Prim x))
verifyPrim Phase ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap phase (V.eval (Prim x))
verifyPrim Conjugate ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap conjugate (V.eval (Prim x))
verifyPrim I2N ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessNum (undefined :: Prim b) = do
    fmap i2n (V.eval (Prim x))
verifyPrim I2B ((x :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessNum (undefined :: Prim b) = do
    x <- V.eval (Prim x)
    return (V.fromSMT (SMT.not (x V..==. 0)))
verifyPrim B2I (x :* Nil)
  | Dict <- V.witnessNum (undefined :: Prim (DenResult a)) = do
    x <- V.eval (Prim x)
    return (V.smtIte (V.toSMT x) 1 0)
verifyPrim Round ((x :: ASTF SoftwarePrimDomain b) :* Nil) = do
  x <- V.eval (Prim x)
  return (fromRat (toRat x))
verifyPrim Not (x :* Nil) =
  fmap (V.fromSMT . SMT.not . V.toSMT) (V.eval (Prim x))
verifyPrim And (x :* y :* Nil) = do
  x <- V.eval (Prim x)
  y <- V.eval (Prim y)
  return (V.fromSMT (V.toSMT x SMT..&&. V.toSMT y))
verifyPrim Or (x :* y :* Nil) = do
  x <- V.eval (Prim x)
  y <- V.eval (Prim y)
  return (V.fromSMT (V.toSMT x SMT..||. V.toSMT y))
verifyPrim Eq ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (V..==.) (V.eval (Prim x)) (V.eval (Prim y)))
verifyPrim Neq ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (./=.) (V.eval (Prim x)) (V.eval (Prim y)))
  where
    x ./=. y = SMT.not (x V..==. y)
verifyPrim Lt ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessOrd  (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (V..<.) (V.eval (Prim x)) (V.eval (Prim y)))
verifyPrim Gt ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessOrd  (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (V..>.) (V.eval (Prim x)) (V.eval (Prim y)))
verifyPrim Lte ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessOrd  (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (V..<=.) (V.eval (Prim x)) (V.eval (Prim y)))
verifyPrim Gte ((x :: ASTF SoftwarePrimDomain b) :* y :* Nil)
  | Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- V.witnessOrd  (undefined :: Prim b) =
    fmap V.fromSMT (S.liftM2 (V..>=.) (V.eval (Prim x)) (V.eval (Prim y)))
verifyPrim BitAnd (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    S.liftM2 (.&.) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim BitOr (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    S.liftM2 (.|.) (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim BitXor (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    S.liftM2 xor (V.eval (Prim x)) (V.eval (Prim y))
verifyPrim BitCompl (x :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    fmap complement (V.eval (Prim x))
verifyPrim ShiftL (x :* (y :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)),
    Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- witnessIntegral (undefined :: Prim b) = do
    -- XXX should check for undefined behaviour
    x <- V.eval (Prim x)
    y <- V.eval (Prim y)
    return (shiftL x (i2n y))
verifyPrim ShiftR (x :* (y :: ASTF SoftwarePrimDomain b) :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)),
    Dict <- V.witnessPred (undefined :: Prim b),
    Dict <- witnessIntegral (undefined :: Prim b) = do
    -- XXX should check for undefined behaviour
    x <- V.eval (Prim x)
    y <- V.eval (Prim y)
    return (shiftR x (i2n y))
verifyPrim (ArrIx (Imp.IArrComp name :: Imp.IArr Index b)) (i :* Nil) = do
  i <- V.eval (Prim i)
  readArray name i
verifyPrim Cond (cond :* x :* y :* Nil) =
  S.liftM3 V.smtIte
    (fmap V.toSMT (V.eval (Prim cond)))
    (V.eval (Prim x))
    (V.eval (Prim y))
verifyPrim exp _ = error ("Unimplemented: " ++ show exp)

--------------------------------------------------------------------------------
