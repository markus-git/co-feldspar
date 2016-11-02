{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Hardware.Frontend where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Representation

import Data.Struct

import Data.Constraint hiding (Sub)
import Data.Proxy

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- hardware-edsl.
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp

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
-- ** Hardware instructions.

--------------------------------------------------------------------------------
-- *** Singals.



--------------------------------------------------------------------------------
-- *** Structural entities.

--------------------------------------------------------------------------------
