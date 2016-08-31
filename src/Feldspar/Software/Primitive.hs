{-# language GADTs #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}

module Feldspar.Software.Primitive where

import Feldspar.Primitive
import Feldspar.Representation

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

--------------------------------------------------------------------------------
-- * Software Types.
--------------------------------------------------------------------------------

data SoftwareTypeRep a
  where
    -- booleans
    BoolST   :: SoftwareTypeRep Bool
    -- signed numbers.
    Int8ST   :: SoftwareTypeRep Int8
--  Int16ST  :: SoftwareTypeRep Int16
--  Int32ST  :: SoftwareTypeRep Int32
--  Int64ST  :: SoftwareTypeRep Int64
    -- unsigned numbers.
    Word8ST  :: SoftwareTypeRep Word8
--  Word16ST :: SoftwareTypeRep Word16
--  Word32ST :: SoftwareTypeRep Word32
--  Word64ST :: SoftwareTypeRep Word64
    -- floating point numbers.
    FloatST  :: SoftwareTypeRep Float
--  DoulbeST :: SoftwareTypeRep Double

deriving instance Eq       (SoftwareTypeRep a)
deriving instance Show     (SoftwareTypeRep a)
deriving instance Typeable (SoftwareTypeRep a)

--------------------------------------------------------------------------------

class (Eq a, Show a, Typeable a) => SoftwareType a
  where
    softwareRep :: SoftwareTypeRep a

instance SoftwareType Bool  where softwareRep = BoolST
instance SoftwareType Int8  where softwareRep = Int8ST
instance SoftwareType Word8 where softwareRep = Word8ST

--------------------------------------------------------------------------------

-- ...

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

type Length = Int8
type Index  = Int8

-- | For loop.
data ForLoop sig
  where
    ForLoop :: Type st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

deriving instance Eq       (ForLoop a)
deriving instance Show     (ForLoop a)
deriving instance Typeable (ForLoop a)

--------------------------------------------------------------------------------

-- | ...
type SoftwareConstructs = CoConstructs :+: ForLoop

-- | ...
type SoftwareDomain = SoftwareConstructs :&: TypeRepF

-- | Software expressions.
newtype Data a = Data { unData :: ASTF SoftwareDomain a }

--------------------------------------------------------------------------------

instance Syn (Data a)
  where
    type C (Data a) = Data
    type I (Data a) = a

    desug = id
    sug   = id
    trep  = undefined

--------------------------------------------------------------------------------
-- ...

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
