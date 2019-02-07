{-# language GADTs                      #-}
{-# language ConstraintKinds            #-}
{-# language TypeOperators              #-}
{-# language TypeFamilies               #-}
{-# language MultiParamTypeClasses      #-}
{-# language FlexibleContexts           #-}
{-# language FlexibleInstances          #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}

module Feldspar.Software.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Storable
import Feldspar.Array.Buffered (ArraysEq(..))
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Data.Struct

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Constraint
import Control.Monad.Reader (ReaderT(..), runReaderT, lift)

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam)
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal, Mode)
import qualified Language.Embedded.Hardware.Command as Imp
import qualified Language.Embedded.Hardware.Expression.Represent as Imp

import Prelude hiding ((==))
import qualified Prelude as P

-- hmm!
import Feldspar.Hardware.Frontend (HSig)

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

data AssertCMD fs a
  where
    Assert :: AssertionLabel
           -> exp Bool
           -> String
           -> AssertCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor AssertCMD
  where
    hfmap _ (Assert lbl cond msg) = Assert lbl cond msg

instance Oper.HBifunctor AssertCMD
  where
    hbimap _ g (Assert lbl cond msg) = Assert lbl (g cond) msg

instance Oper.InterpBi AssertCMD IO (Oper.Param1 SoftwarePrimType)
  where
    interpBi (Assert _ cond msg) = do
      cond' <- cond
      unless cond' $ error $ "Assertion failed: " ++ msg

--------------------------------------------------------------------------------

-- | Soften the hardware signature of a component into a type that uses the
--   correspoinding data types in software.
type family Soften a where
  Soften ()                   = ()
  Soften (Imp.Signal  a -> b) = Ref (SExp a) -> Soften b
  Soften (Imp.Array i a -> b) = Arr (SExp a) -> Soften b

-- | Software argument for a hardware component.
data Argument pred a
  where
    Nil  :: Argument pred ()
    ARef :: (pred a, Integral a, Imp.PrimType a)
         => Ref (SExp a)
         -> Argument pred b
         -> Argument pred (Ref (SExp a) -> b)
    AArr :: (pred a, Integral a, Imp.PrimType a)
         => Arr (SExp a)
         -> Argument pred b
         -> Argument pred (Arr (SExp a) -> b)

-- | Software component, consists of a hardware signature and its address.
data Address a = Address String (HSig a)

-- | ...
data MMapCMD fs a
  where
    MMap :: String
         -> HSig a
         -> MMapCMD (Oper.Param3 prog exp pred) String
    Call :: Address a
         -> Argument pred (Soften a)
         -> MMapCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor MMapCMD
  where
    hfmap f (MMap s sig)    = MMap s sig
    hfmap f (Call addr arg) = Call addr arg

instance Oper.HBifunctor MMapCMD
  where
    hbimap g f (MMap s sig)    = MMap s sig
    hbimap g f (Call addr arg) = Call addr arg

instance (MMapCMD Oper.:<: instr) => Oper.Reexpressible MMapCMD instr env
  where
    reexpressInstrEnv reexp (MMap s sig)    = lift $ singleInj $ MMap s sig
    reexpressInstrEnv reexp (Call addr arg) = lift $ singleInj $ Call addr arg

instance Oper.InterpBi MMapCMD IO (Param1 SoftwarePrimType)
  where
    interpBi = error "todo: interpBi of mmap."

--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
    -- ^ Computational instructions.
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.ArrCMD
    -- ^ Software specific instructions.
  Oper.:+: Imp.FileCMD
  Oper.:+: AssertCMD  
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
-- ** ...
--------------------------------------------------------------------------------

instance ArraysEq Arr IArr
  where
    unsafeArrEq (Arr _ _ arr) (IArr _ _ brr) =
      and (zipListStruct sameId arr brr)
      where
        sameId :: Imp.Arr Index a -> Imp.IArr Index a -> Bool
        sameId (Imp.ArrComp a) (Imp.IArrComp b) = a P.== b
        sameId _ _ = False

--------------------------------------------------------------------------------

type instance Expr     Software = SExp
type instance DomainOf Software = SoftwareDomain

--------------------------------------------------------------------------------

instance (Reference Software ~ Ref, Type SoftwarePrimType a) =>
    Storable Software (SExp a)
  where
    type StoreRep Software (SExp a) = Ref (SExp a)
    type StoreSize Software (SExp a) = ()
    newStoreRep _ _      = newRef
    initStoreRep         = initRef
    readStoreRep         = getRef
    unsafeFreezeStoreRep = unsafeFreezeRef
    writeStoreRep        = setRef

--------------------------------------------------------------------------------
