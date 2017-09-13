{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language GeneralizedNewtypeDeriving #-}

module Feldspar.Hardware.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Common
import Feldspar.Frontend
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Expression
import Data.Struct

import Data.Array ((!))
import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Proxy
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
import Language.Embedded.Hardware.Expression.Represent (Inhabited(..))
import qualified Language.Embedded.Hardware.Command   as Imp
import qualified Language.Embedded.Hardware.Interface as Imp

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Hardware instructions.
type HardwareCMD =
           Imp.VariableCMD
  Oper.:+: Imp.VArrayCMD
  Oper.:+: Imp.LoopCMD
  Oper.:+: Imp.ConditionalCMD
    -- ^ Computatonal instructions.
  Oper.:+: Imp.SignalCMD
  Oper.:+: Imp.ArrayCMD
  Oper.:+: Imp.StructuralCMD
  Oper.:+: Imp.ComponentCMD
    -- ^ Hardware specific instructions.

-- | Monad for building software programs in Feldspar.
newtype Hardware a = Hardware { unHardware :: Program HardwareCMD (Param2 HExp HardwarePrimType) a}
  deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

-- | Hardware references.
newtype Ref a = Ref { unRef :: Struct HardwarePrimType Imp.Variable (Internal a) }

-- | Hardware arrays.
data Arr a = Arr
  { arrOffset :: HExp Integer
  , arrLength :: HExp Integer
  , unArr     :: Struct HardwarePrimType (Imp.VArray) (Internal a)
  }

-- | Immutable hardware arrays.
data IArr a = IArr
  { iarrOffset :: HExp Integer
  , iarrLength :: HExp Integer
  , unIArr     :: Struct HardwarePrimType (Imp.IArray) (Internal a)
  }

-- | Hardware arrays of signals.
data SArr a = SArr
  { sarrOffset :: HExp Integer
  , sarrLength :: HExp Integer
  , unSArr     :: Struct HardwarePrimType (Imp.Array) (Internal a)
  }

-- | Hardware signatures.
type Sig = Signature (Param3 Hardware HExp HardwarePrimType)

--------------------------------------------------------------------------------

-- ... hmm ...
type instance Expr Hardware = HExp
type instance DomainOf Hardware = HardwareDomain

--------------------------------------------------------------------------------
