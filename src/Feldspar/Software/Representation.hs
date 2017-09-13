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
import Feldspar.Software.Expression
import Data.Struct

-- ... hmm ...
import Feldspar.Hardware.Representation (Sig)

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

-- ... hmm ...
type instance Expr Software = SExp
type instance DomainOf Software = SoftwareDomain

--------------------------------------------------------------------------------
