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

module Feldspar.Software.Representation where

import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Software.Primitive

import Data.Struct
import Data.Inhabited

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Proxy
import Data.Constraint

import Language.Syntactic as S
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

import Control.Monad.Operational.Higher as O hiding ((:<:))

import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD = CompCMD O.:+: Imp.FileCMD

-- | Monad for building software programs in Feldspar.
newtype Software a = Software { unSoftware ::
    ProgramT SoftwareCMD (Param2 Data SoftwarePrimType)
      (Program CompCMD (Param2 Data SoftwarePrimType))
        a
  } deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------
-- * Expression.
--------------------------------------------------------------------------------

type Length = Int8
type Index  = Int8

-- | For loop.
data ForLoop sig
  where
    ForLoop :: Syntax st =>
        ForLoop (Length :-> st :-> (Index -> st -> st) :-> Full st)

deriving instance Eq       (ForLoop a)
deriving instance Show     (ForLoop a)
deriving instance Typeable (ForLoop a)

--------------------------------------------------------------------------------

-- | Software symbols.
type SoftwareConstructs = ForLoop S.:+: SoftwarePrimConstructs

-- | Software symbols tagged with their type representation.
type SoftwareDomain = SoftwareConstructs :&: TypeRepF SoftwarePrimType SoftwarePrimTypeRep

-- | Software expressions.
newtype Data a = Data { unData :: ASTF SoftwareDomain a }

-- | ...
type instance ExprOf SoftwareDomain = Data
type instance PredOf SoftwareDomain = SoftwarePrimType    -- ? 
type instance TRepOf SoftwareDomain = SoftwarePrimTypeRep -- ?

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> Internal a
eval = evalClosed . desugar

--------------------------------------------------------------------------------

instance Syntactic (Data a)
  where
    type Domain   (Data a) = SoftwareDomain
    type Internal (Data a) = a

    desugar = unData
    sugar   = Data

-- | ...
sugarSymSoftware
    :: ( Signature sig
       , fi             ~ SmartFun SoftwareDomain sig
       , sig            ~ SmartSig fi
       , SoftwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , SoftwareType (DenResult sig)
       )
    => sub sig -> f
sugarSymSoftware = sugarSymDecor $ ValT $ typeRep (Proxy :: Proxy SoftwareDomain)

-- | ...
sugarSymPrimSoftware
    :: ( Signature sig
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
-- imperative-edsl instances.

instance Imp.FreeExp Data
  where
    type FreePred Data = SoftwareType
    constExp = sugarSymSoftware . Lit
    varExp   = sugarSymSoftware . FreeVar

--------------------------------------------------------------------------------
-- syntactic isntances.

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
-- * Types.
--------------------------------------------------------------------------------

instance Type SoftwareDomain Bool  where typeRep _ = Node BoolST
instance Type SoftwareDomain Int8  where typeRep _ = Node Int8ST
instance Type SoftwareDomain Word8 where typeRep _ = Node Word8ST

--------------------------------------------------------------------------------

class    (Type SoftwareDomain a, SoftwarePrimType a) => SoftwareType a
instance (Type SoftwareDomain a, SoftwarePrimType a) => SoftwareType a

--------------------------------------------------------------------------------
{-
sTypeEq :: STypeRep a -> STypeRep b -> Maybe (Dict (a ~ b))
sTypeEq (Node t)       (Node u) = sPrimTypeEq t u
sTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- sTypeEq t1 t2
  Dict <- sTypeEq u1 u2
  return Dict
sTypeEq _ _ = Nothing

sTypeRep :: Struct SoftwarePrimType c a -> STypeRep a
sTypeRep = mapStruct (const softwareRep)
-}
--------------------------------------------------------------------------------
