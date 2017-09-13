{-# language GADTs                 #-}
{-# language TypeFamilies          #-}
{-# language TypeOperators         #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language UndecidableInstances  #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds       #-}
{-# language StandaloneDeriving    #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Hardware.Expression where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Hardware.Primitive
import Data.Struct

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Constraint
import Data.Typeable (Typeable)

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam)
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

-- hardware-edsl.
import Language.Embedded.Hardware.Interface

--------------------------------------------------------------------------------
-- * Hardware expressions.
--------------------------------------------------------------------------------

type instance PredicateOf      HardwareDomain   = HardwarePrimType
type instance RepresentationOf HardwarePrimType = HardwarePrimTypeRep

--------------------------------------------------------------------------------
-- ** Hardware types.

-- | Representation of supported hardware types.
type HTypeRep = TypeRep HardwarePrimType HardwarePrimTypeRep

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

-- | Compare two hardware types for equality.
hardwareTypeEq :: HTypeRep a -> HTypeRep b -> Maybe (Dict (a ~ b))
hardwareTypeEq (Node t)       (Node u) = hardwarePrimTypeEq t u
hardwareTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- hardwareTypeEq t1 t2
  Dict <- hardwareTypeEq u1 u2
  return Dict
hardwareTypeEq _ _ = Nothing

-- | Construct the hardware type representation of 'a'.
hardwareTypeRep :: Struct HardwarePrimType c a -> HTypeRep a
hardwareTypeRep = mapStruct (const hardwareRep)

--------------------------------------------------------------------------------

-- | Short-hand for hardware types.
type HType    = Type HardwarePrimType

-- | Short-hand for primitive hardware types.
type HType'   = PrimType HardwarePrimType

--------------------------------------------------------------------------------
-- ** Hardware expression symbols.

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

-- | Evaluate a closed hardware expression.
eval :: (Syntactic a, Domain a ~ HardwareDomain) => a -> Internal a
eval = evalClosed . desugar

-- | Sugar a software symbol as a smart constructor.
sugarSymHardware
    :: ( Syn.Signature sig
       , fi  ~ SmartFun dom sig
       , sig ~ SmartSig fi
       , dom ~ SmartSym fi
       , dom ~ HardwareDomain
       , SyntacticN f fi
       , sub :<: HardwareConstructs
       , Type HardwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymHardware = sugarSymDecor $ ValT $ typeRep

-- | Sugar a software symbol as a smart primitive constructor.
sugarSymPrimHardware
    :: ( Syn.Signature sig
       , fi  ~ SmartFun dom sig
       , sig ~ SmartSig fi
       , dom ~ SmartSym fi
       , dom ~ HardwareDomain
       , SyntacticN f fi
       , sub :<: HardwareConstructs
       , HardwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymPrimHardware = sugarSymDecor $ ValT $ Node hardwareRep

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
      ValT (Branch ta tb) -> Branch
        (sugarSymDecor (ValT ta) Fst a)
        (sugarSymDecor (ValT tb) Snd a)
      FunT _ _ -> error "Syntactic can't sugar a function."

instance Tuples HardwareDomain
  where
    pair   = sugarSymHardware Pair
    first  = sugarSymHardware Fst
    second = sugarSymHardware Snd

instance FreeExp HExp
  where
    type PredicateExp HExp = PrimType HardwarePrimType
    litE = sugarSymHardware . Lit
    varE = sugarSymHardware . FreeVar

--------------------------------------------------------------------------------
