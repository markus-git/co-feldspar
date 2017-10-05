{-# language TypeFamilies          #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances  #-}
{-# language Rank2Types            #-}
{-# language ScopedTypeVariables   #-}

module Feldspar.Hardware.Frontend where

import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Sugar
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Feldspar.Hardware.Representation
import Data.Struct

import Control.Monad.Identity (Identity)
import Data.Constraint hiding (Sub)
import Data.Int
import Data.List (genericLength)
import Data.Proxy

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal, Ident, Mode)
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp

import Prelude hiding (length)

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

instance Value HExp
  where
    value = sugarSymHardware . Lit

instance Share HExp
  where
    share = sugarSymHardware (Let "")

instance Loop HExp
  where
    loop = sugarSymHardware ForLoop

instance Cond HExp
  where
    cond = sugarSymHardware Cond

instance Equality HExp
  where
    (==) = sugarSymPrimHardware Eq

instance Ordered HExp
  where
    (<)  = sugarSymPrimHardware Lt
    (<=) = sugarSymPrimHardware Lte
    (>)  = sugarSymPrimHardware Gt
    (>=) = sugarSymPrimHardware Gte

instance Logical HExp
  where
    not  = sugarSymPrimHardware Not
    (&&) = sugarSymPrimHardware And
    (||) = sugarSymPrimHardware Or

instance Multiplicative HExp
  where
    mult = sugarSymPrimHardware Mul
    div  = sugarSymPrimHardware Div
    mod  = sugarSymPrimHardware Mod

instance Bitwise HExp
  where
    complement = sugarSymPrimHardware BitCompl
    (.&.) = sugarSymPrimHardware BitAnd
    (.|.) = sugarSymPrimHardware BitOr
    xor   = sugarSymPrimHardware BitXor
    sll   = sugarSymPrimHardware ShiftL
    srl   = sugarSymPrimHardware ShiftR
    rol   = sugarSymPrimHardware RotateL
    ror   = sugarSymPrimHardware RotateR

instance Casting HExp
  where
    i2n = sugarSymPrimHardware I2N

--------------------------------------------------------------------------------

instance (Bounded a, HType a) => Bounded (HExp a)
  where
    minBound = value minBound
    maxBound = value maxBound

instance (Num a, HType' a) => Num (HExp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSymHardware Add
    (-)         = sugarSymHardware Sub
    (*)         = sugarSymHardware Mul
    negate      = sugarSymHardware Neg
    abs         = error "abs not implemeted for `HExp`"
    signum      = error "signum not implemented for `HExp`"

--------------------------------------------------------------------------------
-- * Instructions.
--------------------------------------------------------------------------------

desugar :: (Syntactic a, Domain a ~ HardwareDomain) => a -> HExp (Internal a)
desugar = HExp . Syntactic.desugar

sugar   :: (Syntactic a, Domain a ~ HardwareDomain) => HExp (Internal a) -> a
sugar   = Syntactic.sugar . unHExp

resugar
  :: ( Syntactic a
     , Syntactic b
     , Internal a ~ Internal b
     , Domain a   ~ HardwareDomain
     , Domain b   ~ HardwareDomain
     )
  => a -> b
resugar = Syntactic.resugar

--------------------------------------------------------------------------------

-- Swap an `Imp.FreePred` constraint with a `HardwarePrimType` one.
withHType :: forall a b . Proxy a
  -> (Imp.PredicateExp HExp a => b)
  -> (HardwarePrimType      a => b)
withHType _ f = case hardwareDict (hardwareRep :: HardwarePrimTypeRep a) of
  Dict -> f

-- Proves that a `HardwarePrimTypeRep a` type satisfies `Imp.FreePred`.
hardwareDict :: HardwarePrimTypeRep a -> Dict (Imp.PredicateExp HExp a)
hardwareDict rep = case rep of
  BoolHT    -> Dict
  IntegerHT -> Dict
  Int8HT    -> Dict
  Int16HT   -> Dict
  Int32HT   -> Dict
  Int64HT   -> Dict
  Word8HT   -> Dict
  Word16HT  -> Dict
  Word32HT  -> Dict
  Word64HT  -> Dict

--------------------------------------------------------------------------------

instance References Hardware
  where
    type Reference Hardware = Ref    
    initRef    = Hardware . fmap Ref . mapStructA (Imp.initVariable) . resugar
    newRef     = Hardware . fmap Ref . mapStructA (const Imp.newVariable) $ typeRep
    getRef     = Hardware . fmap resugar . mapStructA getRef' . unRef
    setRef ref
      = Hardware
      . sequence_
      . zipListStruct setRef' (unRef ref)
      . resugar
    unsafeFreezeRef
      = Hardware
      . fmap resugar
      . mapStructA freezeRef'
      . unRef

-- 'Imp.getRef' specialized hardware.
getRef' :: forall b . HardwarePrimType b => Imp.Variable b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getRef' = withHType (Proxy :: Proxy b) Imp.getVariable

-- 'Imp.setRef' specialized to hardware.
setRef' :: forall b . HardwarePrimType b => Imp.Variable b -> HExp b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setRef' = withHType (Proxy :: Proxy b) Imp.setVariable

-- 'Imp.unsafeFreezeRef' specialized to hardware.
freezeRef' :: forall b . HardwarePrimType b => Imp.Variable b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
freezeRef' = withHType (Proxy :: Proxy b) Imp.unsafeFreezeVariable

--------------------------------------------------------------------------------

instance Slicable HExp (Arr a)
  where
    slice from len (Arr o l arr) = Arr (o+from) len arr

instance Finite HExp (Arr a)
  where
    length = arrLength

instance Finite HExp (SArr a)
  where
    length = sarrLength

instance Arrays Hardware
  where
    type Array Hardware = Arr
    newArr len
      = Hardware
      $ fmap (Arr 0 len)
      $ mapStructA (const (Imp.newVArray len))
      $ typeRep
    initArr as
      = Hardware
      $ fmap (Arr 0 len . Node)
      $ Imp.initVArray as
      where len = value $ genericLength as
    getArr arr ix
      = Hardware
      $ fmap resugar
      $ mapStructA (flip getArr' (ix + arrOffset arr))
      $ unArr arr
    setArr arr ix a
      = Hardware
      $ sequence_
      $ zipListStruct (\v a -> setArr' a (ix + arrOffset arr) v) (resugar a)
      $ unArr arr
    copyArr arr brr
      = Hardware
      $ sequence_
      $ zipListStruct (\a b ->
          Imp.copyVArray (a, arrOffset arr) (b, arrOffset brr) (length brr))
        (unArr arr)
        (unArr brr)

-- 'Imp.getVArr' specialized to hardware.
getArr' :: forall b . HardwarePrimType b => Imp.VArray Index b -> HExp Index -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getArr' = withHType (Proxy :: Proxy b) Imp.getVArray

-- 'Imp.setVArr' specialized to hardware.
setArr' :: forall b . HardwarePrimType b => Imp.VArray Index b -> HExp Index -> HExp b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setArr' = withHType (Proxy :: Proxy b) Imp.setVArray

--------------------------------------------------------------------------------

instance Syntax HExp a => Indexed HExp (IArr a)
  where
    type Elem (IArr a) = a
    (!) (IArr off len a) ix = resugar $ mapStruct index a
      where
        index :: HardwarePrimType b => Imp.IArray Index b -> HExp b
        index arr = sugarSymPrimHardware (ArrIx arr) (ix + off)

instance Slicable HExp (IArr a)
  where
    slice from len (IArr o l arr) = IArr (o+from) len arr

instance Finite HExp (IArr a)
  where
    length = iarrLength
      
instance IArrays Hardware
  where
    type IArray Hardware = IArr
    unsafeFreezeArr arr
      = Hardware
      $ fmap (IArr (arrOffset arr) (length arr))
      $ mapStructA (Imp.unsafeFreezeVArray)
      $ unArr arr
    unsafeThawArr iarr
      = Hardware
      $ fmap (Arr (iarrOffset iarr) (length iarr))
      $ mapStructA (Imp.unsafeThawVArray)
      $ unIArr iarr

--------------------------------------------------------------------------------

instance Control Hardware
  where
    iff c t f
      = Hardware
      $ Imp.iff (resugar c)
          (unHardware t)
          (unHardware f)
    while c body
      = Hardware
      $ Imp.while
          (fmap resugar $ unHardware c)
          (unHardware body)
    for lower upper body
      = Hardware
      $ Imp.for
          (resugar lower)
          (resugar upper)
          (unHardware . body . resugar)

--------------------------------------------------------------------------------
-- ** Hardware instructions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- *** Singals.

-- | Creates a new signal with a given initial value.
initSignal :: HType' a => HExp a -> Hardware (Signal a)
initSignal = Hardware . Imp.initSignal

-- | Creates a new signal.
newSignal :: HType' a => Hardware (Signal a)
newSignal = Hardware $ Imp.newSignal

-- | Get the current value of a signal.
getSignal :: HType' a => Signal a -> Hardware (HExp a)
getSignal = Hardware . Imp.getSignal

-- | Set the current value of a signal.
setSignal :: HType' a => Signal a -> HExp a -> Hardware ()
setSignal s = Hardware . (Imp.setSignal s)

--------------------------------------------------------------------------------
-- *** Signal arrays.
--------------------------------------------------------------------------------
-- todo: These functions could use some cleaning up. 'Internal' is not really
--       necessary here, its better to assume 'SArr (HExp a)'.
--------------------------------------------------------------------------------

newArray :: HType (Internal a) => HExp Index -> Hardware (SArr a)
newArray len = Hardware $ fmap (SArr 0 len) $ mapStructA (const (Imp.newArray len)) $ typeRep

initArray :: HType' (Internal a) => [Internal a] -> Hardware (SArr a)
initArray as = Hardware $ fmap (SArr 0 len . Node) $ Imp.initArray as
  where len = value $ genericLength as

getArray :: HType (Internal a) => SArr a -> HExp Index -> Hardware (HExp (Internal a))
getArray arr ix = Hardware $ fmap resugar $ mapStructA (flip getSArr' (ix + sarrOffset arr)) $ (unSArr arr)

setArray :: HType (Internal a) => SArr a -> HExp Index -> HExp (Internal a) -> Hardware ()
setArray arr ix a = Hardware $ sequence_ $ zipListStruct (\v a -> setSArr' a (ix + sarrOffset arr) v) (resugar a) $ unSArr arr

copyArray :: HType (Internal a) => SArr a -> SArr a -> Hardware ()
copyArray arr brr = Hardware $ sequence_ $ zipListStruct (\a b -> Imp.copyArray (a, sarrOffset arr) (b, sarrOffset brr) (length brr)) (unSArr arr) (unSArr brr)

--------------------------------------------------------------------------------

-- 'Imp.getArray' specialized to hardware.
getSArr' :: forall b . HardwarePrimType b => Imp.Array Index b -> HExp Index -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getSArr' = withHType (Proxy :: Proxy b) Imp.getArray

-- 'Imp.setArray' specialized to hardware.
setSArr' :: forall b . HardwarePrimType b => Imp.Array Index b -> HExp Index -> HExp b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setSArr' = withHType (Proxy :: Proxy b) Imp.setArray

--------------------------------------------------------------------------------
-- *** Structural entities.

entity  :: String -> Hardware () -> Hardware ()
entity name = Hardware . (Imp.entity name) . unHardware

architecture :: String -> String -> Hardware () -> Hardware ()
architecture entity name = Hardware . (Imp.architecture entity name) . unHardware

process :: [Ident] -> Hardware () -> Hardware ()
process is = Hardware . (Imp.process is) . unHardware

--------------------------------------------------------------------------------

-- | Declare a port signal and assig its initial value.
initPort :: HardwarePrimType a => Mode -> HExp a -> Hardware (Signal a)
initPort m e = Hardware $ Imp.initPort m e

-- | Declare a port.
newPort :: HardwarePrimType a => Mode -> Hardware (Signal a)
newPort m  = Hardware $ Imp.newPort m

--------------------------------------------------------------------------------
-- *** Components.
{-
-- short-hand for hardware signatures.
type HSignature = Imp.Sig HardwareCMD HExp HardwarePrimType Identity

-- short-hand for hardware components.
type HComponent = Imp.Comp HardwareCMD HExp HardwarePrimType Identity

-- short-hand for arguments to hardware signatures.
type HArgument  = Imp.Argument HardwarePrimType

namedComponent :: String -> Sig a -> Hardware (HComponent a)
namedComponent n sig = Hardware $ Imp.namedComponent n $ toHardware sig
  where
    toHardware :: Sig a -> HSignature a
    toHardware (SigRet p)           = Imp.Ret (unHardware p)
    toHardware (SigSignal n m   sf) = Imp.SSig n m (toHardware . sf)
    toHardware (SigArray  n m l af) = Imp.SArr n m (toInteger l) (toHardware . af)

component :: Sig a -> Hardware (HComponent a)
component = namedComponent "comp"

portmap :: HComponent a -> HArgument a -> Hardware ()
portmap c = Hardware . Imp.portmap c

ret :: Hardware () -> Sig ()
ret = SigRet

output :: FType' a => (Signal a -> Hardware ()) -> Sig (Signal a -> ())
output f = SigSignal (Imp.Base "out") Imp.Out $ \sig -> ret (f sig)

input :: FType' a => (Signal a -> Sig b) -> Sig (Signal a -> b)
input = SigSignal (Imp.Base "in") Imp.In

outputArr :: FType' a
  => Integer
  -> (SArr (HExp a) -> Hardware ())
  -> Sig (Imp.Array a -> ())
outputArr len f = SigArray (Imp.Base "out") Imp.Out (fromIntegral len) $ \arr ->
  ret $ f $ SArr 0 (value len) $ Node arr

inputArr :: FType' a
  => Integer
  -> (SArr (HExp a) -> Sig b) -> Sig (Imp.Array a -> b)
inputArr len f = SigArray (Imp.Base "in") Imp.In (fromIntegral len) $ \arr ->
  f $ SArr 0 (value len) $ Node arr
-}
--------------------------------------------------------------------------------
