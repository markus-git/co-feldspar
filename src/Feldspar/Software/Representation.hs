{-# language GADTs                      #-}
{-# language TypeOperators              #-}
{-# language TypeFamilies               #-}
{-# language MultiParamTypeClasses      #-}
{-# language FlexibleContexts           #-}
{-# language FlexibleInstances          #-}
{-# language GeneralizedNewtypeDeriving #-}

module Feldspar.Software.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Storable
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Command
import Data.Struct

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Constraint

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

-- debug.
--import Debug.Trace

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
    -- ^ Computational instructions.
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.ArrCMD
    -- ^ Software specific instructions.
  Oper.:+: Imp.FileCMD

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

-- ... hmm ...
type instance Expr Software = SExp
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
-- *** Temporary hot-fix until GHC fixes their class resolution for DTC ***

bug :: String -> Bool
bug = const True
--bug msg = trace msg True

instance {-# OVERLAPPING #-} Project sub SoftwareConstructs =>
    Project sub (AST SoftwareDomain)
  where
    prj (Sym s) | bug "Sym" = Syn.prj s
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project sub SoftwareConstructs =>
    Project sub SoftwareDomain
  where
    prj (expr :&: info) | bug "(:&:)" = Syn.prj expr
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project BindingT SoftwareConstructs
  where
    prj (InjL a) | bug "BindingT" = Just a
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project Let SoftwareConstructs
  where
    prj (InjR (InjL a)) | bug "Let" = Just a
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project Tuple SoftwareConstructs
  where
    prj (InjR (InjR (InjL a))) | bug "Tuple" = Just a
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project SoftwarePrimConstructs SoftwareConstructs
  where
    prj (InjR (InjR (InjR (InjL a)))) | bug "Prim" = Just a
    prj _ = Nothing

instance {-# OVERLAPPING #-} Project ForLoop SoftwareConstructs
  where
    prj (InjR (InjR (InjR (InjR a)))) | bug "Loop" = Just a
    prj _ = Nothing

--------------------------------------------------------------------------------
