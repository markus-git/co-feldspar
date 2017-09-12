{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}
{-# language PolyKinds #-}
{-# language ConstraintKinds #-}

module Feldspar.Common where

import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Software.Primitive
import Feldspar.Hardware.Primitive

import Data.Int
import Data.Word

-- operational-higher.
import Control.Monad.Operational.Higher

-- imperative-edsl.
import qualified Language.Embedded.Expression as S
import qualified Language.Embedded.Imperative as S

-- hardware-edsl.
import qualified Language.Embedded.Hardware.Command   as H
import qualified Language.Embedded.Hardware.Interface as H

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- ... software types ...
type SType    = Type SoftwarePrimType

-- ... software primitive types ...
type SType'   = PrimType SoftwarePrimType

--------------------------------------------------------------------------------

-- ... hardware types ...
type HType    = Type HardwarePrimType

-- ... hardware primitive types ...
type HType'   = PrimType HardwarePrimType

--------------------------------------------------------------------------------

-- ... software and hardware types ...
type FType  a = (SType  a, HType  a)

-- ... software and hardware primitive types ...
type FType' a = (SType' a, HType' a)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Signature description of a hardware component.
data Signature fs a
  where
    SigRet
      :: prog () -> Signature (Param3 prog exp pred) ()
    SigSignal
      :: (FType' a, pred a) => H.Name -> H.Mode
      -> (H.Signal a -> Signature (Param3 prog exp pred) b)
      -> Signature (Param3 prog exp pred) (H.Signal a -> b)
    SigArray
      :: (FType' a, pred a) => H.Name -> H.Mode -> Int32
      -> (H.Array a -> Signature (Param3 prog exp pred) b)
      -> Signature (Param3 prog exp pred) (H.Array a -> b)

-- | Arguments for a hardware component.
data HArg a
  where
    HardNil :: HArg ()
    HardSig :: HType' a => H.Signal a -> HArg b -> HArg (H.Signal a -> b)
    HardArr :: HType' a => H.Array  a -> HArg b -> HArg (H.Array  a -> b)

--------------------------------------------------------------------------------

-- | Software signature description of a hardware component.
data Address a
  where
    AddrRet
      :: Address ()
    AddrRef
      :: SType' a => S.Ref Int32
      -> (S.Ref a -> Address b)
      -> Address (S.Ref a -> b)
    AddrArr
      :: SType' a => S.Ref Int32 -> Int32
      -> (S.Arr Index a -> Address b)
      -> Address (S.Arr Index a -> b)

-- | Arguments for a software component.
data SArg a
  where
    SoftNil :: SArg ()
    SoftRef :: SType' a => S.Ref a       -> SArg b -> SArg (S.Ref a -> b)
    SoftArr :: SType' a => S.Arr Index a -> SArg b -> SArg (S.Arr Index a -> b)

--------------------------------------------------------------------------------
