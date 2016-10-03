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

import Control.Monad.Trans

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

instance MonadComp Software
  where
    type Expr Software = Data
    type Pred Software = SoftwarePrimType
    type TRep Software = SoftwarePrimTypeRep

    liftComp = Software . lift

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

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> Internal a
eval = evalClosed . desugar

--------------------------------------------------------------------------------

type instance ExprOf SoftwareDomain = Data
type instance ExprOf Data           = SoftwareDomain

type instance PredOf SoftwareDomain = SoftwarePrimType    -- ?
type instance PredOf Data           = SoftwareType

type instance TRepOf SoftwareDomain = SoftwarePrimTypeRep -- ?
type instance TRepOf Data           = SoftwarePrimTypeRep

--------------------------------------------------------------------------------

instance Syntactic (Data a)
  where
    type Domain   (Data a) = SoftwareDomain
    type Internal (Data a) = a

    desugar = unData
    sugar   = Data

instance Syntactic (Struct SoftwarePrimType Data a)
  where
    type Domain   (Struct SoftwarePrimType Data a) = SoftwareDomain
    type Internal (Struct SoftwarePrimType Data a) = a

    desugar = undefined
    sugar   = undefined

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

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
instance Type SoftwareDomain Float where typeRep _ = Node FloatST

--------------------------------------------------------------------------------

class    (Type SoftwareDomain a, SoftwarePrimType a) => SoftwareType a
instance (Type SoftwareDomain a, SoftwarePrimType a) => SoftwareType a

--------------------------------------------------------------------------------

type SoftwareTypeRep = TypeRep SoftwarePrimType SoftwarePrimTypeRep

--------------------------------------------------------------------------------

instance Type SoftwareDomain a => Syntax (Data a)

--------------------------------------------------------------------------------

instance TypeDict SoftwareDomain
  where
    withType :: forall proxy1 proxy2 a b
      .  proxy1 SoftwareDomain
      -> proxy2 a
      -> (Imp.FreePred Data a => b)
      -> (SoftwarePrimType  a => b)
    withType pd pa f = case softwareDict (softwareRep :: SoftwarePrimTypeRep a) of
      Dict -> f

softwareDict :: SoftwarePrimTypeRep a -> Dict (Imp.FreePred Data a)
softwareDict rep = case rep of
  BoolST  -> Dict
  Int8ST  -> Dict
  Word8ST -> Dict
  FloatST -> Dict

--------------------------------------------------------------------------------

softwareTypeEq :: SoftwareTypeRep a -> SoftwareTypeRep b -> Maybe (Dict (a ~ b))
softwareTypeEq (Node t)       (Node u) = softwarePrimTypeEq t u
softwareTypeEq (Branch t1 u1) (Branch t2 u2) = do
  Dict <- softwareTypeEq t1 t2
  Dict <- softwareTypeEq u1 u2
  return Dict
softwareTypeEq _ _ = Nothing

softwareTypeRep :: Struct SoftwarePrimType c a -> SoftwareTypeRep a
softwareTypeRep = mapStruct (const softwareRep)

--------------------------------------------------------------------------------
