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
{-# language ConstraintKinds #-}

module Feldspar.Software.Representation where

import Feldspar.Sugar
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

import Control.Monad.Operational.Higher as Oper hiding ((:<:))

import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.FileCMD

-- | Monad for building software programs in Feldspar.
newtype Software a = Software { unSoftware :: Program SoftwareCMD (Param2 SExp SoftwarePrimType) a }
  deriving (Functor, Applicative, Monad)

--------------------------------------------------------------------------------

-- | Software reference.
newtype Ref a = Ref { unRef :: Struct SoftwarePrimType Imp.Ref (Internal a) }

--------------------------------------------------------------------------------
-- * Expression.
--------------------------------------------------------------------------------

type Length = Int8
type Index  = Int8

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
  S.:+: ForLoop
  S.:+: Tuple
  S.:+: Let
  S.:+: BindingT

-- | Software symbols tagged with their type representation.
type SoftwareDomain = SoftwareConstructs :&: TypeRepF SoftwarePrimType SoftwarePrimTypeRep

-- | Software expressions.
newtype SExp a = SExp { unSExp :: ASTF SoftwareDomain a }

-- | Evaluate a closed expression
eval :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> Internal a
eval = evalClosed . desugar

-- | ...
type instance Pred SoftwareDomain = SoftwarePrimType

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
  :: ( Signature sig
       , fi             ~ SmartFun SoftwareDomain sig
       , sig            ~ SmartSig fi
       , SoftwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , SType (DenResult sig)
       )
    => sub sig -> f
sugarSymSoftware = sugarSymDecor $ ValT $ typeRep

--------------------------------------------------------------------------------

sugarSymPrimSoftware
    :: ( Signature sig
       , fi             ~ SmartFun SoftwareDomain sig
       , sig            ~ SmartSig fi
       , SoftwareDomain ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: SoftwareConstructs
       , SPrimType (DenResult sig)
       )
    => sub sig -> f
sugarSymPrimSoftware = sugarSymDecor $ ValT $ Node softwareRep

--------------------------------------------------------------------------------
-- imperative-edsl instances.

instance Imp.FreeExp SExp
  where
    type FreePred SExp = SPrimType
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
-- * Types.
--------------------------------------------------------------------------------

instance Type SoftwarePrimType Bool  where typeRep = Node BoolST
instance Type SoftwarePrimType Int8  where typeRep = Node Int8ST
instance Type SoftwarePrimType Word8 where typeRep = Node Word8ST
instance Type SoftwarePrimType Float where typeRep = Node FloatST

--------------------------------------------------------------------------------

-- ... software type representation ...
type STypeRep = TypeRep SoftwarePrimType SoftwarePrimTypeRep

-- ... software types ...
type SType = Type SoftwarePrimType

--------------------------------------------------------------------------------

-- ... text ...
class    (SType a, SoftwarePrimType a) => SPrimType a
instance (SType a, SoftwarePrimType a) => SPrimType a

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
{-
instance Syntax Software (SExp Bool)
instance Syntax Software (SExp Int8)
instance Syntax Software (SExp Word8)
instance Syntax Software (SExp Float)
instance
  ( Syntax Software a, Domain a ~ SoftwareDomain
  , Syntax Software b, Domain b ~ SoftwareDomain
  )
    => Syntax Software (a, b)
-}
--------------------------------------------------------------------------------
