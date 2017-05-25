{-# language StandaloneDeriving #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}

{-# language InstanceSigs #-}
{-# language Rank2Types #-}
{-# language ConstraintKinds #-}

module Feldspar.Hardware.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Common
import Feldspar.Frontend

import Feldspar.Hardware.Primitive

import Data.Struct
import Data.Inhabited

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

--------------------------------------------------------------------------------
-- ** Instructions.
--------------------------------------------------------------------------------

type Sig = Signature (Param3 Hardware HExp HardwarePrimType)

--------------------------------------------------------------------------------
-- ** Expression.
--------------------------------------------------------------------------------

-- | Hardware symbols.
type HardwareConstructs =
        HardwarePrimConstructs
  Syn.:+: Tuple
  Syn.:+: Let
  Syn.:+: BindingT

-- | Hardware symbols tagged with their type representation.
type HardwareDomain = HardwareConstructs :&: TypeRepF HardwarePrimType HardwarePrimTypeRep

-- | Hardware expressions.
newtype HExp a = HExp { unHExp :: ASTF HardwareDomain a }

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ HardwareDomain) => a -> Internal a
eval = evalClosed . desugar

--------------------------------------------------------------------------------

-- ... hmm ...
type instance Expr Hardware = HExp

-- ...
type instance DomainOf         Hardware         = HardwareDomain
type instance PredicateOf      HardwareDomain   = HardwarePrimType
type instance RepresentationOf HardwarePrimType = HardwarePrimTypeRep

--------------------------------------------------------------------------------

instance Syntactic (HExp a)
  where
    type Domain   (HExp a) = HardwareDomain
    type Internal (HExp a) = a

    desugar = unHExp
    sugar   = HExp

instance Syntactic (Struct HardwarePrimType HExp a)
  where
    type Domain   (Struct HardwarePrimType HExp a) = HardwareDomain
    type Internal (Struct HardwarePrimType HExp a) = a

    desugar (Node a)     = unHExp a
    desugar (Branch a b) = sugarSymDecor (ValT $ Branch ta tb) Pair a' b'
      where
        a' = desugar a
        b' = desugar b
        ValT ta = getDecor a'
        ValT tb = getDecor b'

    sugar a = case getDecor a of
      ValT (Node _)       -> Node $ HExp a
      ValT (Branch ta tb) -> Branch (sugarSymDecor (ValT ta) Fst a) (sugarSymDecor (ValT tb) Snd a)

--------------------------------------------------------------------------------

sugarSymHardware
    :: ( Syn.Signature sig
       , fi             ~ SmartFun HardwareDomain sig
       , sig            ~ SmartSig fi
       , HardwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: HardwareConstructs
       , Type HardwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymHardware = sugarSymDecor $ ValT $ typeRep

--------------------------------------------------------------------------------

sugarSymPrimHardware
    :: ( Syn.Signature sig
       , fi             ~ SmartFun HardwareDomain sig
       , sig            ~ SmartSig fi
       , HardwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: HardwareConstructs
       , HardwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymPrimHardware = sugarSymDecor $ ValT $ Node hardwareRep

--------------------------------------------------------------------------------

instance Tuples HardwareDomain
  where
    pair   = sugarSymHardware Pair
    first  = sugarSymHardware Fst
    second = sugarSymHardware Snd

--------------------------------------------------------------------------------
-- hardware-edsl instances.

instance Imp.FreeExp HExp
  where
    type PredicateExp HExp = PrimType HardwarePrimType
    litE = sugarSymHardware . Lit
    varE = sugarSymHardware . FreeVar

--------------------------------------------------------------------------------
-- ** Types.
--------------------------------------------------------------------------------

-- ... hardware type representation ...
type HTypeRep = TypeRep HardwarePrimType HardwarePrimTypeRep

--------------------------------------------------------------------------------

instance Type HardwarePrimType Bool    where typeRep = Node BoolHT
instance Type HardwarePrimType Integer where typeRep = Node IntegerHT
instance Type HardwarePrimType Int8    where typeRep = Node Int8HT
instance Type HardwarePrimType Int16   where typeRep = Node Int16HT
instance Type HardwarePrimType Int32   where typeRep = Node Int32HT
instance Type HardwarePrimType Int64   where typeRep = Node Int64HT
instance Type HardwarePrimType Word8   where typeRep = Node Word8HT
instance Type HardwarePrimType Word16  where typeRep = Node Word16HT
instance Type HardwarePrimType Word32  where typeRep = Node Word32HT
instance Type HardwarePrimType Word64  where typeRep = Node Word64HT

--------------------------------------------------------------------------------

hardwareTypeEq :: HTypeRep a -> HTypeRep b -> Maybe (Dict (a ~ b))
hardwareTypeEq (Node t)       (Node u) = hardwarePrimTypeEq t u
hardwareTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- hardwareTypeEq t1 t2
  Dict <- hardwareTypeEq u1 u2
  return Dict
hardwareTypeEq _ _ = Nothing

hardwareTypeRep :: Struct HardwarePrimType c a -> HTypeRep a
hardwareTypeRep = mapStruct (const hardwareRep)

--------------------------------------------------------------------------------
{-
instance Syntax Hardware (HExp Bool)
instance Syntax Hardware (HExp Int8)
instance Syntax Hardware (HExp Word8)
instance
  ( Syntax Hardware a, Domain a ~ HardwareDomain
  , Syntax Hardware b, Domain b ~ HardwareDomain
  )
    => Syntax Hardware (a, b)
-}
--------------------------------------------------------------------------------
