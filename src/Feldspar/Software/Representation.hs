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

import Feldspar.Primitive
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Sugar
import Data.Inhabited

import Feldspar.Software.Primitive

import Control.Monad.Trans

import Data.Int
import Data.Word
import Data.List (genericTake)
import Data.Typeable (Typeable)
import Data.Proxy
import Data.Struct

import Language.Syntactic hiding (Syntactic(..), SyntacticN(..), SmartFun, sugarSymDecor)
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

import qualified Control.Monad.Operational.Higher as Oper

import qualified Language.Embedded.Imperative as Imp

import qualified Language.Syntactic as S

--------------------------------------------------------------------------------
-- * ... types ...
--------------------------------------------------------------------------------

type instance RepOf Data = SoftwareTypeRep

instance Type Data Bool  where typeRep _ = Node softwareRep
instance Type Data Int8  where typeRep _ = Node softwareRep
instance Type Data Word8 where typeRep _ = Node softwareRep

--------------------------------------------------------------------------------
-- * ... expressions ...
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
type SoftwareConstructs = ForLoop :+: SoftwarePrimitiveConstructs

-- | Software symbols tagged with their type representation.
type SoftwareDomain = SoftwareConstructs :&: TypeRepF SoftwarePrimType SoftwareTypeRep

-- | Software expressions.
newtype Data a = Data { unData :: ASTFull SoftwareDomain a }

--------------------------------------------------------------------------------

type instance PredOf Data = SoftwarePrimType

instance Syntactic (Data a)
  where
    type Constructor (Data a) = ASTFull SoftwareDomain
    type Internal    (Data a) = a
    desugar = unData
    sugar   = Data

--------------------------------------------------------------------------------

sugarSymSoft
  :: ( -- its an OK signature
       Signature sig
       -- internal (hi) of internal (fi) is a function over `ASTF`.
     , hi             ~ S.SmartFun SoftwareDomain sig
     , S.SmartSig fi  ~ S.SmartSig hi
     , S.SmartSym fi  ~ S.SmartSym hi
     , S.SyntacticN fi hi
       -- internal (fi) of our function (f) is a function over `ASTFull`.
     , fi             ~ SmartFull SoftwareDomain sig
     , sig            ~ S.SmartSig fi
     , SoftwareDomain ~ S.SmartSym fi
     , SyntacticN f fi
       -- lifted symbol is part of our set software symbols.
     , sub :<: SoftwareConstructs
       -- its type is representable in our set of software types.
     , SoftwarePrimType (S.DenResult sig)
     )
  => sub sig -> f
sugarSymSoft = sugarN . sugarSymDecor (ValT $ Node $ softwareRep)

--------------------------------------------------------------------------------

instance NUM Data where
  plus   = sugarSymSoft Add
  minus  = sugarSymSoft Sub
  times  = sugarSymSoft Mul
  negate = sugarSymSoft Neg

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | ...
type SoftwareCMD = CoCMD Oper.:+: Imp.FileCMD

-- | Monad for building software programs in Feldspar.
newtype Software a = Software { runSoftware ::
    Oper.ProgramT SoftwareCMD (Oper.Param2 Data SoftwarePrimType)
      (Oper.Program CoCMD (Oper.Param2 Data SoftwarePrimType))
      a
  } deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

instance MonadComp Software
  where
    type Expr Software = Data
    type Pred Software = SoftwarePrimType

    liftComp = Software . lift

--------------------------------------------------------------------------------

-- ...

--------------------------------------------------------------------------------
-- ... syntactic isntances ...
--------------------------------------------------------------------------------

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
