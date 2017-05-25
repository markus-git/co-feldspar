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
{-# language PolyKinds #-}

{-# language InstanceSigs #-}
{-# language Rank2Types #-}
{-# language ConstraintKinds #-}

module Feldspar.Software.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Common
import Feldspar.Frontend

import Feldspar.Software.Primitive

import Feldspar.Hardware.Representation (Sig)

import Data.Struct
import Data.Inhabited

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Proxy
import Data.Constraint

import Control.Monad.Reader (ReaderT(..), runReaderT, lift)

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam)
import Language.Syntactic.Functional.Tuple

import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher as Oper hiding ((:<:))

-- imperative-edsl.
import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp

-- hardware-edsl
import qualified Language.Embedded.Hardware.Command   as H
import qualified Language.Embedded.Hardware.Interface as H

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.ArrCMD
    -- ^ Computational instructions.
  Oper.:+: Imp.FileCMD
    -- ^ Software specific instructions.
  Oper.:+: MMapCMD

-- | Monad for building software programs in Feldspar.
newtype Software a = Software { unSoftware :: Program SoftwareCMD (Param2 SExp SoftwarePrimType) a }
  deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

-- | Software reference.
newtype Ref a = Ref { unRef :: Struct SoftwarePrimType Imp.Ref (Internal a) }

-- | Software array.
data Arr a = Arr
  { arrOffset :: SExp Index
  , arrLength :: SExp Length
  , unArr     :: Struct SoftwarePrimType (Imp.Arr Index) (Internal a)
  }

-- | Immutable software array.
data IArr a = IArr
  { iarrOffset :: SExp Index
  , iarrLength :: SExp Length
  , unIArr     :: Struct SoftwarePrimType (Imp.IArr Index) (Internal a)
  }


--------------------------------------------------------------------------------
-- ** Instructions.
--------------------------------------------------------------------------------

-- todo : must it really be closed?
type family Soften a where
  Soften () = ()
  Soften (H.Signal a -> b) = Imp.Ref a       -> Soften b
  Soften (H.Array  a -> b) = Imp.Arr Index a -> Soften b

-- todo : these two families could probably be better.
type family Result a where
  Result ()                    = ()
  Result (Imp.Ref a -> ())       = Ref (SExp a)
  Result (Imp.Ref a -> b)        = Result b
  Result (Imp.Arr Index a -> ()) = Arr (SExp a)
  Result (Imp.Arr Index a -> b)  = Result b

-- todo : yep, most likely.
type family Argument a where
  Argument ()        = ()
  Argument (a -> ()) = ()
  Argument (a -> b)  = a -> Argument b

--------------------------------------------------------------------------------

data MMapCMD fs a
  where
    MMap :: String -> Sig a
         -> MMapCMD (Param3 prog exp pred) (Address (Soften a))
    Call :: Address a -> SArg (Argument a)
         -> MMapCMD (Param3 prog exp pred) (Result a)

-- todo : I ignore translations for the signature. I think this is correct,
--        since the software side should not touch the hardware program inside,
--        but I should double check this later. This todo goes for all
--        instance declarations below.
instance Oper.HFunctor MMapCMD
  where
    hfmap _ (MMap n sig)     = MMap n sig
    hfmap _ (Call addr args) = Call addr args

instance Oper.HBifunctor MMapCMD
  where
    hbimap _ _ (MMap n sig)     = MMap n sig
    hbimap _ _ (Call addr args) = Call addr args

instance (MMapCMD Imp.:<: instr) => Oper.Reexpressible MMapCMD instr env
  where
    reexpressInstrEnv reexp (MMap n sig) = ReaderT $ \env ->
      Oper.singleInj $ MMap n sig
    reexpressInstrEnv reexp (Call addr args) = ReaderT $ \env ->
      Oper.singleInj $ Call addr args

--------------------------------------------------------------------------------
-- ** Expression.
--------------------------------------------------------------------------------

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
  Syn.:+: ForLoop
  Syn.:+: Tuple
  Syn.:+: Let
  Syn.:+: BindingT

-- | Software symbols tagged with their type representation.
type SoftwareDomain = SoftwareConstructs :&: TypeRepF SoftwarePrimType SoftwarePrimTypeRep

-- | Software expressions.
newtype SExp a = SExp { unSExp :: ASTF SoftwareDomain a }

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> Internal a
eval = evalClosed . desugar

--------------------------------------------------------------------------------

-- ... hmm ...
type instance Expr Software = SExp

-- ...
type instance DomainOf         Software         = SoftwareDomain
type instance PredicateOf      SoftwareDomain   = SoftwarePrimType
type instance RepresentationOf SoftwarePrimType = SoftwarePrimTypeRep

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
      ValT (Branch ta tb) -> Branch (sugarSymDecor (ValT ta) Fst a) (sugarSymDecor (ValT tb) Snd a)

--------------------------------------------------------------------------------

sugarSymSoftware
  :: ( Syn.Signature sig
       , fi             ~ SmartFun SoftwareDomain sig
       , sig            ~ SmartSig fi
       , SoftwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , Type SoftwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymSoftware = sugarSymDecor $ ValT $ typeRep

--------------------------------------------------------------------------------

sugarSymPrimSoftware
    :: ( Syn.Signature sig
       , fi             ~ SmartFun SoftwareDomain sig
       , sig            ~ SmartSig fi
       , SoftwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , SoftwarePrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymPrimSoftware = sugarSymDecor $ ValT $ Node softwareRep

--------------------------------------------------------------------------------

instance Tuples SoftwareDomain
  where
    pair   = sugarSymSoftware Pair
    first  = sugarSymSoftware Fst
    second = sugarSymSoftware Snd

--------------------------------------------------------------------------------
-- imperative-edsl instances.

instance Imp.FreeExp SExp
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
-- ** Types.
--------------------------------------------------------------------------------

-- ... software type representation ...
type STypeRep = TypeRep SoftwarePrimType SoftwarePrimTypeRep

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

softwareTypeEq :: STypeRep a -> STypeRep b -> Maybe (Dict (a ~ b))
softwareTypeEq (Node t)       (Node u) = softwarePrimTypeEq t u
softwareTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- softwareTypeEq t1 t2
  Dict <- softwareTypeEq u1 u2
  return Dict
softwareTypeEq _ _ = Nothing

softwareTypeRep :: Struct SoftwarePrimType c a -> STypeRep a
softwareTypeRep = mapStruct (const softwareRep)

--------------------------------------------------------------------------------
