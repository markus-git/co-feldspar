{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Hardware.Frontend where

import Prelude hiding (length)

import Data.Constraint hiding (Sub)
import Data.Proxy

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal, Ident)
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp

import Data.Struct

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Representation

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** General constructs.

instance Value HardwareDomain
  where
    value = sugarSymHardware . Lit

instance Share HardwareDomain
  where
    share = sugarSymHardware (Let "")

--------------------------------------------------------------------------------
-- ** Primitive functions.

instance Equality HardwareDomain
  where
    (==) = sugarSymHardware Eq

instance Ordered HardwareDomain
  where
    (<)  = sugarSymHardware Lt

instance Logical HardwareDomain
  where
    not  = sugarSymHardware Not
    (&&) = sugarSymHardware And

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

instance Indexed HardwareDomain (HExp Index) (IArr a)
  where
    type Elem (IArr a) = a

    (!) (IArr off len a) ix = resugar $ mapStruct index a
      where
        index :: HardwarePrimType b => Imp.IArray Index b -> HExp b
        index arr = sugarSymPrimHardware (ArrIx arr) (ix + off)

instance Finite (HExp Index) (Arr a)  where length = arrLength
instance Finite (HExp Index) (IArr a) where length = iarrLength

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

-- ...
withHType :: forall a b . Proxy a -> (Imp.PredicateExp HExp a => b) -> (HardwarePrimType a => b)
withHType _ f = case hardwareDict (hardwareRep :: HardwarePrimTypeRep a) of
  Dict -> f

-- ...
hardwareDict :: HardwarePrimTypeRep a -> Dict (Imp.PredicateExp HExp a)
hardwareDict rep = case rep of
  BoolHT   -> Dict
  Int8HT   -> Dict
  Word8HT  -> Dict

--------------------------------------------------------------------------------
-- ** General instructions.

instance References Hardware
  where
    type Reference Hardware = Ref
    
    initRef    = Hardware . fmap Ref . mapStructA (Imp.initVariable) . resugar
    newRef     = Hardware . fmap Ref . mapStructA (const Imp.newVariable) $ typeRep
    getRef     = Hardware . fmap resugar . mapStructA getRef' . unRef
    setRef ref = Hardware . sequence_ . zipListStruct setRef' (unRef ref) . resugar

-- Imp.getRef specialized a software constraint.
getRef' :: forall b . HardwarePrimType b
  => Imp.Variable b
  -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getRef' = withHType (Proxy :: Proxy b) Imp.getVariable

-- Imp.setRef specialized to a software constraint.
setRef' :: forall b . HardwarePrimType b
  => Imp.Variable b -> HExp b
  -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setRef' = withHType (Proxy :: Proxy b) Imp.setVariable

--------------------------------------------------------------------------------

instance Arrays Hardware
  where
    type Array Hardware = Arr
    type Ix    Hardware = HExp Index
    
    newArr len
      = Hardware
      $ fmap (Arr 0 len)
      $ mapStructA (const (Imp.newVArray len))
      $ typeRep

    getArr arr ix
      = Hardware
      $ fmap resugar
      $ mapStructA (getArr' (ix + arrOffset arr))
      $ unArr arr

    setArr arr ix a
      = Hardware
      $ sequence_
      $ zipListStruct (setArr' (ix + arrOffset arr)) (resugar a)
      $ unArr arr

getArr' :: forall b . HardwarePrimType b
  => HExp Index -> Imp.VArray Index b
  -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) (HExp b)
getArr' = withHType (Proxy :: Proxy b) Imp.getVArray

setArr' :: forall b . HardwarePrimType b
  => HExp Index -> HExp b -> Imp.VArray Index b
  -> Oper.Program HardwareCMD (Oper.Param2 HExp HardwarePrimType) ()
setArr' = withHType (Proxy :: Proxy b) Imp.setVArray

--------------------------------------------------------------------------------

instance IArrays Hardware
  where
    type IArray Hardware = IArr

    freezeArr arr
      = Hardware
      $ fmap (IArr (arrOffset arr) (length arr))
      $ mapStructA (flip Imp.freezeArray (length arr))
      $ unArr arr

    thawArr iarr
      = error "todo: thawArr for hardware"

--------------------------------------------------------------------------------
-- ** Hardware instructions.

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
-- *** Structural entities.

entity  :: String -> Hardware () -> Hardware ()
entity name = Hardware . (Imp.entity name) . unHardware

-- *** todo : entity name should be derived from context, not explicitly stated here.
architecture :: String -> String -> Hardware () -> Hardware ()
architecture entity name = Hardware . (Imp.architecture entity name) . unHardware

process :: [Ident] -> Hardware () -> Hardware ()
process is = Hardware . (Imp.process is) . unHardware

--------------------------------------------------------------------------------
