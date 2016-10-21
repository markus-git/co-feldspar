{-# language TypeOperators #-}
{-# language StandaloneDeriving #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# language TypeFamilies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language FlexibleContexts #-}
{-# language ScopedTypeVariables #-}

{-# language InstanceSigs #-}
{-# language Rank2Types #-}
{-# language ConstraintKinds #-}

module Feldspar.Hardware.Representation where

import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Hardware.Primitive

import Data.Struct
import Data.Inhabited

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Proxy
import Data.Constraint

import Control.Monad.Trans

import Language.Syntactic as S
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

import Control.Monad.Operational.Higher as Oper hiding ((:<:))

-- hardware-edsl.
import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Hardware instructions.
type HardwareCMD = CompCMD -- :+: ...

-- | Monad for building software programs in Feldspar.
newtype Hardware a = Hardware { unHardware ::
    ProgramT HardwareCMD (Param2 HExp HardwarePrimType)
      (Program CompCMD (Param2 HExp HardwarePrimType))
        a
  } deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

instance MonadComp Hardware
  where
    type Expr Hardware = HExp
    type Pred Hardware = HardwarePrimType
    type TRep Hardware = HardwarePrimTypeRep

    liftComp = Hardware . lift

--------------------------------------------------------------------------------

newtype Ref a = Ref { unRef :: Struct HardwarePrimType Imp.Ref (Internal a) }

--------------------------------------------------------------------------------
-- * Expression.
--------------------------------------------------------------------------------

-- | Hardware symbols.
type HardwareConstructs =
        HardwarePrimConstructs
  S.:+: Tuple
  S.:+: Let
  S.:+: BindingT

-- | Hardware symbols tagged with their type representation.
type HardwareDomain = HardwareConstructs :&: TypeRepF HardwarePrimType HardwarePrimTypeRep

-- | Hardware expressions.
newtype HExp a = HExp { unHExp :: ASTF HardwareDomain a }

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ HardwareDomain) => a -> Internal a
eval = evalClosed . desugar

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

instance
    ( Syntax Hardware a, Domain a ~ HardwareDomain
    , Syntax Hardware b, Domain b ~ HardwareDomain
    )
      => Syntactic (a, b)
  where
    type Domain   (a, b) = HardwareDomain
    type Internal (a, b) = (Internal a, Internal b)

    desugar (a, b) = sugarSymHardware Pair (desugar a) (desugar b)
    sugar ab       = (sugarSymHardware Fst ab, sugarSymHardware Snd ab)

--------------------------------------------------------------------------------

sugarSymHardware
    :: ( Signature sig
       , fi             ~ SmartFun HardwareDomain sig
       , sig            ~ SmartSig fi
       , HardwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: HardwareConstructs
       , Type HardwarePrimType HardwarePrimTypeRep (DenResult sig)
       )
    => sub sig -> f
sugarSymHardware = sugarSymDecor $ ValT $ typeRep

--------------------------------------------------------------------------------

sugarSymPrimHardware
    :: ( Signature sig
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
-- hardware-edsl instances.
{-
instance Imp.FreeExp HExp
  where
    type PredicateExp HExp = HardwareType
    litE = sugarSymHardware . Lit
    varE = sugarSymHardware . FreeVar
-}
instance Imp.FreeExp HExp
  where
    type FreePred HExp = HardwareType
    constExp = sugarSymHardware . Lit
    varExp   = sugarSymHardware . FreeVar

--------------------------------------------------------------------------------
-- * Types.
--------------------------------------------------------------------------------

instance Type HardwarePrimType HardwarePrimTypeRep Bool  where typeRep = Node BoolHT
instance Type HardwarePrimType HardwarePrimTypeRep Int8  where typeRep = Node Int8HT
instance Type HardwarePrimType HardwarePrimTypeRep Word8 where typeRep = Node Word8HT
--instance Type HardwarePrimType HardwarePrimTypeRep Float where typeRep = Node FloatHT

--------------------------------------------------------------------------------

class    (Type HardwarePrimType HardwarePrimTypeRep a, HardwarePrimType a) => HardwareType a
instance (Type HardwarePrimType HardwarePrimTypeRep a, HardwarePrimType a) => HardwareType a

--------------------------------------------------------------------------------

-- ... hardware type representation ...
type HTypeRep = TypeRep HardwarePrimType HardwarePrimTypeRep

-- ... hardware types ...
type HType = Syntax Hardware

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

instance Syntax Hardware (HExp Bool)
instance Syntax Hardware (HExp Int8)
instance Syntax Hardware (HExp Word8)

instance
  ( Syntax Hardware a, Domain a ~ HardwareDomain
  , Syntax Hardware b, Domain b ~ HardwareDomain
  )
    => Syntax Hardware (a, b)

--------------------------------------------------------------------------------
