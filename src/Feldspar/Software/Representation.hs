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

import Feldspar.Verify.Monad (Verify)
import qualified Feldspar.Verify.FirstOrder as FO
import qualified Feldspar.Verify.Monad as V
import qualified Feldspar.Verify.SMT as SMT
import qualified Feldspar.Verify.Abstract as A

import Data.Array (Ix)
import Data.Constraint hiding ((\\))
import Data.Function (on)
import Data.Functor.Identity
import Data.Maybe (fromMaybe)
import Data.Ord
import Data.IORef
import Data.Int
import Data.Word
import Data.List (genericTake, (\\), sort, sortBy, group, groupBy, intersect, nub)
import Data.Typeable (Typeable, cast, typeOf)
import Data.Struct
import qualified Data.Map.Strict as Map

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

instance (Imp.ControlCMD Oper.:<: instr) => Oper.Reexpressible AssertCMD instr env
  where
    reexpressInstrEnv reexp (Assert lbl cond msg) = do
      cond' <- reexp cond
      lift $ Imp.assert cond' msg

instance FO.HTraversable AssertCMD

instance FO.Symbol AssertCMD
  where
    dry (Assert {}) = return ()

--------------------------------------------------------------------------------

data ControlCMD inv fs a
  where
    If :: exp Bool -> prog () -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    While :: Maybe inv -> prog (exp Bool) -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    For :: (pred i, Integral i) =>
      Maybe inv -> Imp.IxRange (exp i) -> Imp.Val i -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Break :: ControlCMD inv (Oper.Param3 prog exp pred) ()
    --
    Test :: Maybe (exp Bool) -> String ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Hint :: pred a => exp a ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Comment :: String ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor (ControlCMD inv)
  where
    hfmap f ins = runIdentity (FO.htraverse (pure . f) ins)

instance FO.HTraversable (ControlCMD inv)
  where
    htraverse f (If cond tru fls) = (If cond) <$> f tru <*> f fls
    htraverse f (While inv cond body) = (While inv) <$> f cond <*> f body
    htraverse f (For inv range val body) = (For inv range val) <$> f body
    htraverse _ (Break) = pure Break
    htraverse _ (Test cond msg) = pure (Test cond msg)
    htraverse _ (Hint val) = pure (Hint val)
    htraverse _ (Comment msg) = pure (Comment msg)

--------------------------------------------------------------------------------

data PtrCMD fs a
  where
    SwapPtr :: (pred a, Typeable a, pred i, Typeable i, Ix i, Integral i) =>
      Imp.Arr i a -> Imp.Arr i a -> PtrCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor PtrCMD
  where
    hfmap _ (SwapPtr a b) = SwapPtr a b

instance Oper.HBifunctor PtrCMD
  where
    hbimap _ _ (SwapPtr a b) = SwapPtr a b

instance Oper.InterpBi PtrCMD IO (Oper.Param1 SoftwarePrimType)
  where
    interpBi (SwapPtr (Imp.ArrRun a) (Imp.ArrRun b)) = do
      arr <- readIORef a
      brr <- readIORef b
      writeIORef a brr
      writeIORef b arr

instance (PtrCMD Oper.:<: instr) => Oper.Reexpressible PtrCMD instr env
  where
    reexpressInstrEnv reexp (SwapPtr a b) = do
      lift $ Oper.singleInj (SwapPtr a b)

instance FO.HTraversable PtrCMD

instance FO.Symbol PtrCMD
  where
    dry (SwapPtr {}) = return ()

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
         -> MMapCMD (Param3 prog exp pred) String
    Call :: Address a
         -> Argument pred (Soften a)
         -> MMapCMD (Param3 prog exp pred) ()

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

instance FO.HTraversable MMapCMD

instance FO.Symbol MMapCMD
  where
    dry (MMap s sig)    = show <$> FO.fresh
    dry (Call addr sig) = return ()

--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
    -- ^ Computational instructions.
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.ArrCMD
    -- ^ Software specific instructions.
  Oper.:+: Imp.FileCMD
  Oper.:+: Imp.PtrCMD
    -- new stuff
  Oper.:+: AssertCMD
  Oper.:+: PtrCMD
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
-- **
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
