{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language Rank2Types #-}

{-# language ScopedTypeVariables #-}
{-# language InstanceSigs #-}


module Feldspar.Hardware.Frontend where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Representation

import Data.Struct

import Data.Constraint hiding (Sub)
import Data.Proxy

import qualified Control.Monad.Operational.Higher as Oper

-- hardware-edsl.
{-
import qualified Language.Embedded.Hardware.Interface as Imp
import qualified Language.Embedded.Hardware.Command   as Imp
-}

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- syntactic.
import Language.Syntactic

--------------------------------------------------------------------------------
-- * Hardware ...
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Expressions.

instance Value HardwarePrimType HardwarePrimTypeRep HExp
  where
    value = sugarSymHardware . Lit

--------------------------------------------------------------------------------

instance Numerical HardwarePrimType HExp
  where
    plus    = sugarSymPrimHardware Add
    minus   = sugarSymPrimHardware Sub
    times   = sugarSymPrimHardware Mul
    negate  = sugarSymPrimHardware Neg

--------------------------------------------------------------------------------
-- ** Instructions.

-- ...
withHType :: forall a b . Proxy a -> (Imp.FreePred HExp a => b) -> (HardwarePrimType a => b)
withHType _ f = case hardwareDict (hardwareRep :: HardwarePrimTypeRep a) of
  Dict -> f

-- ...
hardwareDict :: HardwarePrimTypeRep a -> Dict (Imp.FreePred HExp a)
hardwareDict rep = case rep of
  BoolHT   -> Dict
  Int8HT   -> Dict
  Word8HT  -> Dict

--------------------------------------------------------------------------------
-- *** ... comp instr ...

instance References Hardware
  where
    type Reference Hardware = Ref

    initRef :: forall a . HType a => a -> Hardware (Ref a)
    initRef
        = liftComp
        . fmap Ref
        . mapStructA (Imp.initRef)
        . construct

    newRef :: forall a . HType a => Hardware (Ref a)
    newRef
        = liftComp
        . fmap Ref
        . mapStructA (const Imp.newRef)
        $ (typeRep :: HTypeRep (Internal a))

    getRef :: HType a => Ref a -> Hardware a
    getRef
        = liftComp
        . fmap destruct
        . mapStructA getty
        . unRef
      where
        getty :: forall b . HardwarePrimType b => Imp.Ref b -> Prog HExp HardwarePrimType (HExp b)
        getty = withHType (Proxy :: Proxy b) Imp.getRef

    setRef :: HType a => Ref a -> a -> Hardware ()
    setRef ref
        = liftComp
        . sequence_
        . zipListStruct setty (unRef ref)
        . construct
      where
        setty :: forall b . HardwarePrimType b => Imp.Ref b -> HExp b -> Prog HExp HardwarePrimType ()
        setty = withHType (Proxy :: Proxy b) Imp.setRef

--------------------------------------------------------------------------------
