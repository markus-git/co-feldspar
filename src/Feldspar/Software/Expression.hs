{-# language GADTs                 #-}
{-# language StandaloneDeriving    #-}
{-# language TypeOperators         #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language UndecidableInstances  #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds       #-}
{-# language TypeFamilies          #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Software.Expression where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Software.Primitive
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

-- imperative-edsl.
import Language.Embedded.Expression

--------------------------------------------------------------------------------
-- * Software expressions.
--------------------------------------------------------------------------------

type instance PredicateOf      SoftwareDomain   = SoftwarePrimType
type instance RepresentationOf SoftwarePrimType = SoftwarePrimTypeRep

--------------------------------------------------------------------------------
-- ** Software types.

-- | Representation of supported software types.
type STypeRep = TypeRep SoftwarePrimType SoftwarePrimTypeRep

instance Type SoftwarePrimType Bool   where typeRep = Node BoolST
instance Type SoftwarePrimType Int8   where typeRep = Node Int8ST
instance Type SoftwarePrimType Int16  where typeRep = Node Int16ST
instance Type SoftwarePrimType Int32  where typeRep = Node Int32ST
instance Type SoftwarePrimType Int64  where typeRep = Node Int64ST
instance Type SoftwarePrimType Word8  where typeRep = Node Word8ST
instance Type SoftwarePrimType Word16 where typeRep = Node Word16ST
instance Type SoftwarePrimType Word32 where typeRep = Node Word32ST
instance Type SoftwarePrimType Word64 where typeRep = Node Word64ST
instance Type SoftwarePrimType Float  where typeRep = Node FloatST
instance Type SoftwarePrimType Double where typeRep = Node DoubleST

-- | Compare two software types for equality.
softwareTypeEq :: STypeRep a -> STypeRep b -> Maybe (Dict (a ~ b))
softwareTypeEq (Node t)       (Node u) = softwarePrimTypeEq t u
softwareTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- softwareTypeEq t1 t2
  Dict <- softwareTypeEq u1 u2
  return Dict
softwareTypeEq _ _ = Nothing

-- | Construct the software type representation of 'a'.
softwareTypeRep :: Struct SoftwarePrimType c a -> STypeRep a
softwareTypeRep = mapStruct (const softwareRep)

--------------------------------------------------------------------------------

-- | Short-hand for software types.
type SType    = Type SoftwarePrimType

-- | Short-hand for primitive software types.
type SType'   = PrimType SoftwarePrimType

--------------------------------------------------------------------------------
-- ** Software expression symbols.

-- | For loop.
data ForLoop sig
  where
    ForLoop :: Syntactic st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

deriving instance Eq       (ForLoop a)
deriving instance Show     (ForLoop a)
deriving instance Typeable (ForLoop a)

--------------------------------------------------------------------------------

-- | Software symbols.
type SoftwareConstructs = 
          SoftwarePrimConstructs
  Syn.:+: Tuple
  Syn.:+: Let
  Syn.:+: BindingT
  -- ^ Software specific symbol.
  Syn.:+: ForLoop

-- | Software symbols tagged with their type representation.
type SoftwareDomain = SoftwareConstructs :&: TypeRepF SoftwarePrimType SoftwarePrimTypeRep

-- | Software expressions.
newtype SExp a = SExp { unSExp :: ASTF SoftwareDomain a }

-- | Evaluate a closed software expression.
eval :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> Internal a
eval = evalClosed . desugar

-- | Sugar a software symbol as a smart constructor.
sugarSymSoftware
  :: ( Syn.Signature sig
       , fi  ~ SmartFun dom sig
       , sig ~ SmartSig fi
       , dom ~ SmartSym fi
       , dom ~ SoftwareDomain
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , Type SoftwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymSoftware = sugarSymDecor $ ValT $ typeRep

-- | Sugar a software symbol as a primitive smart constructor.
sugarSymPrimSoftware
    :: ( Syn.Signature sig
       , fi  ~ SmartFun dom sig
       , sig ~ SmartSig fi
       , dom ~ SmartSym fi
       , dom ~ SoftwareDomain
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , SoftwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymPrimSoftware = sugarSymDecor $ ValT $ Node softwareRep

--------------------------------------------------------------------------------

instance Syntactic (SExp a)
  where
    type Domain   (SExp a) = SoftwareDomain
    type Internal (SExp a) = a

    desugar = unSExp
    sugar   = SExp

instance Syntactic (Struct SoftwarePrimType SExp a)
  where
    type Domain   (Struct SoftwarePrimType SExp a) = SoftwareDomain
    type Internal (Struct SoftwarePrimType SExp a) = a

    desugar (Node a)     = unSExp a
    desugar (Branch a b) = sugarSymDecor (ValT $ Branch ta tb) Pair a' b'
      where
        a' = desugar a
        b' = desugar b
        ValT ta = getDecor a'
        ValT tb = getDecor b'
    
    sugar a = case getDecor a of
      ValT (Node _)       -> Node $ SExp a
      ValT (Branch ta tb) -> Branch
        (sugarSymDecor (ValT ta) Fst a)
        (sugarSymDecor (ValT tb) Snd a)
      FunT _ _ -> error "Syntactic can't sugar a function."

instance Tuples SoftwareDomain
  where
    pair   = sugarSymSoftware Pair
    first  = sugarSymSoftware Fst
    second = sugarSymSoftware Snd

instance FreeExp SExp
  where
    type FreePred SExp = PrimType SoftwarePrimType
    constExp = sugarSymSoftware . Lit
    varExp   = sugarSymSoftware . FreeVar

--------------------------------------------------------------------------------
-- syntactic instances.

instance Eval ForLoop
  where
    evalSym ForLoop = \len init body ->
        foldl (flip body) init $ genericTake len [0..]

instance Symbol ForLoop
  where
    symSig (ForLoop) = signature

instance Render ForLoop
  where
    renderSym  = show
    renderArgs = renderArgsSmart

instance EvalEnv ForLoop env

instance StringTree ForLoop

--------------------------------------------------------------------------------
