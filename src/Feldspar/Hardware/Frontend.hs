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
import Feldspar.Array.Vector hiding (reverse)
import Feldspar.Array.Buffered (ArraysSwap(..))
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Feldspar.Hardware.Representation
import Data.Struct

import Control.Monad.Identity (Identity)
import Data.Constraint hiding (Sub)
import Data.Int
import Data.List (genericLength)
import Data.Proxy
import Data.Typeable (Typeable)

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal, Ident, Mode, ToIdent)
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp
import qualified Language.Embedded.Hardware.Expression.Represent as Imp

import Prelude hiding (length, toInteger)
import qualified Prelude as P

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

instance Value HExp
  where
    value = sugarSymHardware . Lit

instance Share HExp
  where
    share = sugarSymHardware (Let "")

instance Iterate HExp
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
    i2b = error "hardware.todo: i2b"
    b2i = error "hardware.todo: b2i"

cast :: (HardwarePrimType a, HardwarePrimType b) => (a -> b) -> HExp a -> HExp b
cast f = sugarSymPrimHardware (Cast f)

toInteger :: (HardwarePrimType a, Integral a) => HExp a -> HExp Integer
toInteger = cast (fromIntegral)

toUnsigned :: (HardwarePrimType a, Integral a, HardwarePrimType b, Num b) => HExp a -> HExp b
toUnsigned = cast (fromIntegral)

toSigned :: (HardwarePrimType a, Integral a, HardwarePrimType b, Num b) => HExp a -> HExp b
toSigned = cast (fromIntegral)

{-
toBits :: (HardwarePrimType a, Integral a, KnownNat b) => HExp a -> HExp (Bits b)
toBits = cast (bitFrom
-}

toIntegral :: forall a . HardwarePrimType a => Proxy a -> HExp Integer -> HExp a
toIntegral _ = case hardwareRep :: HardwarePrimTypeRep a of
  IntegerHT -> id
  Int8HT    -> toSigned
  Int16HT   -> toSigned
  Int32HT   -> toSigned
  Int64HT   -> toSigned
  Word8HT   -> toUnsigned
  Word16HT  -> toUnsigned
  Word32HT  -> toUnsigned
  Word64HT  -> toUnsigned

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

instance Arrays Hardware
  where
    type Array Hardware = Arr
    newArr len
      = Hardware
      $ fmap (Arr 0 len)
      $ mapStructA (const (Imp.newVArray (toInteger len)))
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
          Imp.copyVArray
            (a, toInteger (arrOffset arr))
            (b, toInteger (arrOffset brr))
            (toInteger (length brr)))
        (unArr arr)
        (unArr brr)

-- 'Imp.getVArr' specialized to hardware.
getArr' :: forall b . HardwarePrimType b => Imp.VArray b -> HExp Index -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getArr' varr ix = withHType (Proxy :: Proxy b) $ Imp.getVArray varr (toInteger ix)

-- 'Imp.setVArr' specialized to hardware.
setArr' :: forall b . HardwarePrimType b => Imp.VArray b -> HExp Index -> HExp b -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setArr' varr ix b = withHType (Proxy :: Proxy b) $ Imp.setVArray varr (toInteger ix) b

--------------------------------------------------------------------------------

instance Syntax HExp a => Indexed HExp (IArr a)
  where
    type ArrElem (IArr a) = a
    (!) (IArr off len a) ix = resugar $ mapStruct index a
      where
        index :: HardwarePrimType b => Imp.IArray b -> HExp b
        index arr = sugarSymPrimHardware (ArrIx arr) (toInteger (ix + off))

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

-- | Short-hand for hardware pull vectors.
type HPull a = Pull HExp a

-- | Short-hand for hardware push vectors.
type HPush a = Push Hardware a

-- | Short-hand for hardware manifest vectors.
type HManifest a = Manifest Hardware a

instance Syntax HExp (HExp a) => Pushy Hardware (IArr (HExp a)) (HExp a)
  where
    toPush iarr = toPush (M iarr :: Manifest Hardware (HExp a))

instance ViewManifest Hardware (IArr (HExp a)) (HExp a)
  where
    viewManifest = Just . M

instance Manifestable Hardware (IArr (HExp a)) (HExp a)    

--------------------------------------------------------------------------------

instance Control Hardware
  where
    iff c t f
      = Hardware
      $ Imp.iff (resugar c)
          (unHardware t)
          (unHardware f)

-- todo: not synthesizable in general, fix to static ranges and add exit.
instance Loop Hardware
  where
    while c body
      = Hardware
      $ Imp.while
          (fmap resugar $ unHardware c)
          (unHardware body)
    for lower _ upper body
      = Hardware
      $ Imp.for
          (resugar (toInteger lower))
          (resugar (toInteger upper))
          (unHardware . body . resugar . toIntegral (proxyE lower))
      where
        proxyE :: forall a . HExp a -> Proxy a
        proxyE _ = Proxy

--------------------------------------------------------------------------------
-- ** Hardware instructions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Singals.
--------------------------------------------------------------------------------

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

-- | Unsafe version of fetching the contents of a signal.
unsafeFreezeSignal :: HType' a => Signal a -> Hardware (HExp a)
unsafeFreezeSignal = Hardware . Imp.unsafeFreezeSignal

-- | ...
veryUnsafeFreezeSignal :: HType' a => Signal a -> HExp a
veryUnsafeFreezeSignal (Imp.SignalC v) = Imp.varE v
veryUnsafeFreezeSignal _ = error "veryUnsafeFreezeSignal shouldn't be used during evaluation."

--------------------------------------------------------------------------------
-- Arrays.
--------------------------------------------------------------------------------

-- | Arrays based on signals.
type SArr a = Imp.Array a

-- | Creates a empty array of the given length.
newSArr :: HType' a => HExp Index -> Hardware (SArr a)
newSArr = Hardware . Imp.newArray . toInteger

-- | Initialize an array with the given elements.
initSArr :: HType' a => [a] -> Hardware (SArr a)
initSArr = Hardware . Imp.initArray

-- | Fetches the indexed element out of the array.
getSArr :: HType' a => SArr a -> HExp Index -> Hardware (HExp a)
getSArr arr ix = Hardware $ Imp.getArray arr (toInteger ix)

-- | Sets the indexed element of the array to the given value.
setSArr :: HType' a => SArr a -> HExp Index -> HExp a -> Hardware ()
setSArr arr ix val = Hardware $ Imp.setArray arr (toInteger ix) val

-- | ...
veryUnsafeFreezeSArr :: HType' a => Length -> SArr a -> IArr (HExp a)
veryUnsafeFreezeSArr len (Imp.ArrayC v) = IArr 0 (value len) $ Node $ Imp.IArrayC v
veryUnsafeFreezeSArr _ _ = error "veryUnsafeFreezeSArr shouldn't be used during evaluation."

--------------------------------------------------------------------------------
-- Components.
--------------------------------------------------------------------------------
-- todo: the `len` argument isn't strictly needed, the problem is that `IArr`
--       length is `HExp Length` while `Imp.copyArray` expects a pure `Length`.

-- | Hardware signature.
type HSig  = Imp.Sig HardwareCMD HExp HardwarePrimType Identity

--------------------------------------------------------------------------------

-- | Finalize signature with an output of a value.
ret :: forall a . (HType' a, Integral a) => Hardware (HExp a) -> HSig (Signal a -> ())
ret prg = withHType' (Proxy :: Proxy a) $ Imp.output $ \o -> Imp.ret $ Imp.process [] $ do
    v <- unHardware prg
    Imp.setSignal o v

retExpr :: forall a . (HType' a, Integral a) => HExp a -> HSig (Signal a -> ())
retExpr expr = ret (return expr)

-- | Finalize signature with an output of a immutable array.
retIArr :: forall a . (HType' a, Integral a) => Length -> Hardware (IArr (HExp a)) -> HSig (SArr a -> ())
retIArr len prg = withHType' (Proxy :: Proxy a) $
  Imp.outputArray (P.toInteger len) $ \o -> Imp.ret $ Imp.process [] $ do
    (IArr _ _ node) <- unHardware prg
    let iarr = case node of (Node iarr) -> iarr
    arr <- Imp.unsafeThawArray iarr
    Imp.copyArray (o,0) (arr,0) (value (P.toInteger len))

-- | Finalize signature with an output of an array.
retVArr :: forall a . (HType' a, Integral a) => Length -> Hardware (Arr (HExp a)) -> HSig (SArr a -> ())
retVArr len prg = withHType' (Proxy :: Proxy a) $
  Imp.outputArray (P.toInteger len) $ \o -> Imp.ret $ Imp.process [] $ do
    (Arr _ _ node) <- unHardware prg
    let arr = case node of (Node arr) -> arr
    iarr <- Imp.unsafeFreezeVArray arr -- this is so bad.
    brr  <- Imp.unsafeThawArray iarr
    Imp.copyArray (o,0) (brr, 0) (value (P.toInteger len))

--------------------------------------------------------------------------------

-- | Extend signature with an input signal.
input :: forall a b . (HType' a, Integral a) => (HExp a -> HSig b) -> HSig (Signal a -> b)
input f = withHType' (Proxy :: Proxy a) $
  Imp.input $ f . veryUnsafeFreezeSignal

-- | Extend signature with an input array.
inputIArr :: forall a b . (HType' a, Integral a) => Length -> (IArr (HExp a) -> HSig b) -> HSig (SArr a -> b)
inputIArr len f = withHType' (Proxy :: Proxy a) $
  Imp.inputArray (P.toInteger len) $ f . veryUnsafeFreezeSArr len

-- inputVec :: forall a b . (HType' a, Integral a) => Lenght -> () -> HSig (SArr a -> b)

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

-- todo: processes...

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

-- Swap an `Imp.FreePred` constraint with a `HardwarePrimType` one.
withHType :: forall a b . Proxy a
  -> (Imp.PredicateExp HExp a => b)
  -> (HardwarePrimType a => b)
withHType _ f = let rep = hardwareRep :: HardwarePrimTypeRep a in
  case predicateDict rep of
    Dict -> f

withHType' :: forall a b . Proxy a
  -> (Imp.Inhabited a => Imp.Sized a => Imp.PrimType a => b)
  -> (HardwarePrimType a => b)
withHType' _ f = let rep = hardwareRep :: HardwarePrimTypeRep a in
  case (inhabitedDict rep, sizedDict rep, repDict rep) of
    (Dict, Dict, Dict) -> f

-- Proves that a `HardwarePrimTypeRep a` type satisfies `Imp.FreePred`.
predicateDict :: HardwarePrimTypeRep a -> Dict (Imp.PredicateExp HExp a)
predicateDict rep = case rep of
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

inhabitedDict :: HardwarePrimTypeRep a -> Dict (Imp.Inhabited a)
inhabitedDict rep = case rep of
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

sizedDict :: HardwarePrimTypeRep a -> Dict (Imp.Sized a)
sizedDict rep = case rep of
  BoolHT    -> Dict
  Int8HT    -> Dict
  Int16HT   -> Dict
  Int32HT   -> Dict
  Int64HT   -> Dict
  Word8HT   -> Dict
  Word16HT  -> Dict
  Word32HT  -> Dict
  Word64HT  -> Dict
  t         -> error ("predicateDict failed for " Prelude.++ show t)

repDict :: HardwarePrimTypeRep a -> Dict (Imp.PrimType a)
repDict rep = case rep of
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

typeableDict :: HardwarePrimTypeRep a -> Dict (Typeable a)
typeableDict rep = case rep of
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
