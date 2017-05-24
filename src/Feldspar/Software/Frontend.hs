{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# language ConstraintKinds #-}
{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}

{-# language InstanceSigs #-}

module Feldspar.Software.Frontend where

import Prelude hiding (length)

import Data.Bits (Bits)
import Data.Constraint hiding (Sub)
import Data.Proxy
import Data.List (genericLength)
import Data.Word hiding (Word)
--import Data.Ix

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

import Data.Struct

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Software.Primitive
import Feldspar.Software.Representation

import Feldspar.Hardware.Representation (Signature)

import Prelude hiding (length, Word)

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** General constructs.

instance Value SoftwareDomain
  where
    value = sugarSymSoftware . Lit

instance Share SoftwareDomain
  where
    share = sugarSymSoftware (Let "")

instance Cond SoftwareDomain
  where
    cond = sugarSymSoftware Cond

--------------------------------------------------------------------------------
-- ** Primitive functions.

instance Equality SoftwareDomain
  where
    (==) = sugarSymSoftware Eq

instance Ordered SoftwareDomain
  where
    (<)  = sugarSymSoftware Lt
    (<=) = sugarSymSoftware Lte
    (>)  = sugarSymSoftware Gt
    (>=) = sugarSymSoftware Gte

instance Logical SoftwareDomain
  where
    not  = sugarSymSoftware Not
    (&&) = sugarSymSoftware And
    (||) = sugarSymSoftware Or

instance Multiplicative SoftwareDomain
  where
    mult = sugarSymSoftware Mul
    div  = sugarSymSoftware Div
    mod  = sugarSymSoftware Mod

instance Bitwise SoftwareDomain
  where
    complement = sugarSymSoftware BitCompl
    (.&.)      = sugarSymSoftware BitAnd
    (.|.)      = sugarSymSoftware BitOr
    xor        = sugarSymSoftware BitXor
    sll        = sugarSymSoftware ShiftL
    srl        = sugarSymSoftware ShiftR
    rol        = sugarSymSoftware RotateL
    ror        = sugarSymSoftware RotateR

instance Casting SoftwareDomain
  where
    i2n = sugarSymSoftware I2N

--------------------------------------------------------------------------------

instance (Bounded a, SType a) => Bounded (SExp a)
  where
    minBound = value minBound
    maxBound = value maxBound

instance (Num a, SType' a) => Num (SExp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSymSoftware Add
    (-)         = sugarSymSoftware Sub
    (*)         = sugarSymSoftware Mul
    negate      = sugarSymSoftware Neg
    abs         = error "todo: abs not implemeted for `SExp`"
    signum      = error "todo: signum not implemented for `SExp`"

--------------------------------------------------------------------------------

instance Indexed SoftwareDomain (SExp Index) (IArr a)
  where
    type Elem (IArr a) = a
    (!) (IArr off len a) ix = resugar $ mapStruct index a
      where
        index :: SoftwarePrimType b => Imp.IArr Index b -> SExp b
        index arr = sugarSymPrimSoftware (ArrIx arr) (ix + off)

instance Slicable (SExp Index) (Arr a)
  where
    slice from len (Arr o l arr) = Arr (o+from) len arr

instance Slicable (SExp Index) (IArr a)
  where
    slice from len (IArr o l arr) = IArr (o+from) len arr

instance Finite (SExp Index) (Arr a)  where length = arrLength
instance Finite (SExp Index) (IArr a) where length = iarrLength

--------------------------------------------------------------------------------
-- * Instructions.
--------------------------------------------------------------------------------

desugar :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> SExp (Internal a)
desugar = SExp . Syntactic.desugar

sugar   :: (Syntactic a, Domain a ~ SoftwareDomain) => SExp (Internal a) -> a
sugar   = Syntactic.sugar . unSExp

resugar
  :: ( Syntactic a
     , Syntactic b
     , Internal a ~ Internal b
     , Domain a   ~ SoftwareDomain
     , Domain b   ~ SoftwareDomain
     )
  => a -> b
resugar = Syntactic.resugar

--------------------------------------------------------------------------------

-- Swap an `Imp.FreePred` constraint with a `SoftwarePrimType` one.
withSType :: forall a b . Proxy a -> (Imp.FreePred SExp a => b) -> (SoftwarePrimType a => b)
withSType _ f = case softwareDict (softwareRep :: SoftwarePrimTypeRep a) of
  Dict -> f

-- Proves that a type from `SoftwarePrimTypeRep` satisfies `Imp.FreePred`.
softwareDict :: SoftwarePrimTypeRep a -> Dict (Imp.FreePred SExp a)
softwareDict rep = case rep of
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

--------------------------------------------------------------------------------
-- ** General instructions.

instance References Software
  where
    type Reference Software = Ref    
    initRef = Software . fmap Ref . mapStructA (Imp.initRef) . resugar
    newRef  = Software . fmap Ref . mapStructA (const Imp.newRef) $ typeRep
    getRef  = Software . fmap resugar . mapStructA getRef' . unRef
    setRef ref
      = Software
      . sequence_
      . zipListStruct setRef' (unRef ref)
      . resugar
    unsafeFreezeRef
      = Software
      . fmap resugar
      . mapStructA freezeRef'
      . unRef

-- Imp.getRef specialized to software.
getRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
getRef' = withSType (Proxy :: Proxy b) Imp.getRef

-- Imp.setRef specialized to software.
setRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> SExp b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) ()
setRef' = withSType (Proxy :: Proxy b) Imp.setRef

-- 'Imp.unsafeFreezeRef' specialized to software.
freezeRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
freezeRef' = withSType (Proxy :: Proxy b) Imp.unsafeFreezeRef

--------------------------------------------------------------------------------

instance Arrays Software
  where
    type Array Software = Arr
    type Ix    Software = SExp Index    
    newArr len
      = Software
      $ fmap (Arr 0 len)
      $ mapStructA (const (Imp.newArr len))
      $ typeRep
    initArr elems
      = Software
      $ fmap (Arr 0 len . Node)
      $ Imp.constArr elems
      where len = value $ genericLength elems      
    getArr arr ix
      = Software
      $ fmap resugar
      $ mapStructA (flip getArr' (ix + arrOffset arr))
      $ unArr arr    
    setArr arr ix a
      = Software
      $ sequence_
      $ zipListStruct
         (\a' arr' -> setArr' arr' (ix + arrOffset arr) a')
         (resugar a)
      $ unArr arr
    copyArr arr brr
      = Software
      $ sequence_
      $ zipListStruct (\a b ->
          Imp.copyArr (a, arrOffset arr) (b, arrOffset brr) (length brr))
        (unArr arr)
        (unArr brr)

-- 'Imp.getArr' specialized to software.
getArr' :: forall b . SoftwarePrimType b => Imp.Arr Index b -> SExp Index -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
getArr' = withSType (Proxy :: Proxy b) Imp.getArr

-- 'Imp.setArr' specialized to software.
setArr' :: forall b . SoftwarePrimType b => Imp.Arr Index b -> SExp Index -> SExp b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) ()
setArr' = withSType (Proxy :: Proxy b) Imp.setArr

--------------------------------------------------------------------------------

instance IArrays Software
  where
    type IArray Software = IArr    
    unsafeFreezeArr arr
      = Software
      $ fmap (IArr (arrOffset arr) (length arr))
      $ mapStructA (Imp.unsafeFreezeArr)
      $ unArr arr
    unsafeThawArr iarr
      = Software
      $ fmap (Arr (iarrOffset iarr) (length iarr))
      $ mapStructA (Imp.unsafeThawArr)
      $ unIArr iarr

--------------------------------------------------------------------------------

instance Control Software
  where
    iff c t f
      = Software
      $ Imp.iff (resugar c)
          (unSoftware t)
          (unSoftware f)      
    while c body
      = Software
      $ Imp.while
          (fmap resugar $ unSoftware c)
          (unSoftware body)
    for lower upper body
      = Software
      $ Imp.for
          (resugar lower, 1, Imp.Incl $ resugar upper)
          (unSoftware . body . resugar)

--------------------------------------------------------------------------------
-- ** Software instructions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- *** File handling.

-- | Open a file.
fopen :: FilePath -> IOMode -> Software Handle
fopen file = Software . Imp.fopen file

-- | Close a file.
fclose :: Handle -> Software ()
fclose = Software . Imp.fclose

-- | Check for end of file.
feof :: Handle -> Software (SExp Bool)
feof = Software . Imp.feof

-- | Put a primitive value to a handle.
fput :: (Formattable a, SType' a)
    => Handle
    -> String  -- Prefix
    -> SExp a  -- Expression to print
    -> String  -- Suffix
    -> Software ()
fput h pre e post = Software $ Imp.fput h pre e post

-- | Get a primitive value from a handle.
fget :: (Formattable a, SType' a) => Handle -> Software (SExp a)
fget = Software . Imp.fget

--------------------------------------------------------------------------------
-- *** Printing.

class PrintfType r
  where
    fprf :: Handle -> String -> [Imp.PrintfArg SExp] -> r

instance (a ~ ()) => PrintfType (Software a)
  where
    fprf h form = Software . Oper.singleInj . Imp.FPrintf h form . reverse

instance (Formattable a, SType' a, PrintfType r) => PrintfType (SExp a -> r)
  where
    fprf h form as = \a -> fprf h form (Imp.PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType r => Handle -> String -> r
fprintf h format = fprf h format []

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType r => String -> r
printf = fprintf Imp.stdout

--------------------------------------------------------------------------------
-- *** Memory.

mmap :: String -> Signature a -> Software (Addr (Soften a))
mmap name sig = Software $ Oper.singleInj $ MMap name sig

call :: Addr a -> Args (Argument a) -> Software (Result a)
call addr args = Software $ Oper.singleInj $ Call addr args

--------------------------------------------------------------------------------
