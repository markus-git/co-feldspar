{-# language GADTs                      #-}
{-# language DataKinds                  #-}
{-# language TypeOperators              #-}
{-# language TypeFamilies               #-}
{-# language MultiParamTypeClasses      #-}
{-# language FlexibleContexts           #-}
{-# language FlexibleInstances          #-}
{-# language GeneralizedNewtypeDeriving #-}

module Feldspar.Hardware.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Storable
import Feldspar.Array.Buffered (ArraysEq(..))
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Data.Struct

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Constraint

import Control.Monad.Identity (Identity)
import Control.Monad.Trans

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam)
import Language.Syntactic.Functional.Tuple

import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher as Oper hiding ((:<:))

-- hardware-edsl.
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp

import Prelude hiding ((==))
import qualified Prelude as P

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Hardware instruction set.
type HardwareCMD =
    -- ^ Computatonal instructions.
           Imp.VariableCMD
  Oper.:+: Imp.VArrayCMD
  Oper.:+: Imp.LoopCMD
  Oper.:+: Imp.ConditionalCMD
    -- ^ Hardware specific instructions.
  Oper.:+: Imp.SignalCMD
  Oper.:+: Imp.ArrayCMD
  Oper.:+: Imp.ProcessCMD
  Oper.:+: Imp.ComponentCMD

-- | Monad for building hardware programs in Co-Feldspar.
newtype Hardware a = Hardware { unHardware :: Program HardwareCMD (Param2 HExp HardwarePrimType) a}
  deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

-- | Hardware references.
newtype Ref a = Ref { unRef :: Struct HardwarePrimType Imp.Variable (Internal a) }

-- | Hardware arrays.
data Arr a = Arr
  { arrOffset :: HExp Index
  , arrLength :: HExp Length
  , unArr     :: Struct HardwarePrimType Imp.VArray (Internal a)
  }

-- | Immutable hardware arrays.
data IArr a = IArr
  { iarrOffset :: HExp Index
  , iarrLength :: HExp Length
  , unIArr     :: Struct HardwarePrimType Imp.IArray (Internal a)
  }

--------------------------------------------------------------------------------
-- ** ...
--------------------------------------------------------------------------------

instance ArraysEq Arr IArr
  where
    unsafeArrEq (Arr _ _ arr) (IArr _ _ brr) =
        and (zipListStruct sameId arr brr)
      where
        sameId :: Imp.VArray a -> Imp.IArray a -> Bool
        sameId (Imp.VArrayC a) (Imp.IArrayC b) = a P.== b
        sameId _ _ = False

--------------------------------------------------------------------------------

type instance Expr     Hardware = HExp
type instance DomainOf Hardware = HardwareDomain

--------------------------------------------------------------------------------

instance (Reference Hardware ~ Ref, Type HardwarePrimType a) =>
    Storable Hardware (HExp a)
  where
    type StoreRep Hardware (HExp a) = Ref (HExp a)
    type StoreSize Hardware (HExp a) = ()
    newStoreRep _ _      = newRef
    initStoreRep         = initRef
    readStoreRep         = getRef
    unsafeFreezeStoreRep = unsafeFreezeRef
    writeStoreRep        = setRef

--------------------------------------------------------------------------------
