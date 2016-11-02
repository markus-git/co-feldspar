{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}
{-# language ConstraintKinds #-}
{-# language Rank2Types #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Software.Frontend where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Software.Primitive
import Feldspar.Software.Representation

import Data.Struct

import Data.Constraint hiding (Sub)
import Data.Proxy

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** General constructs.

instance Value SoftwareDomain
  where
    value = sugarSymSoftware . Lit

instance Share SoftwareDomain
  where
    share = sugarSymSoftware (Let "")

instance Cond SoftwareDomain
  where
    cond t f b = sugarSymSoftware Cond b t f

--------------------------------------------------------------------------------
-- ** Primitive functions.

instance Equality SoftwareDomain
  where
    (==) = sugarSymSoftware Eq

instance Ordered SoftwareDomain
  where
    (<)  = sugarSymSoftware Lt

instance Logical SoftwareDomain
  where
    not  = sugarSymSoftware Not
    (&&) = sugarSymSoftware And

--------------------------------------------------------------------------------

instance (Bounded a, SType a) => Bounded (SExp a)
  where
    minBound = value minBound
    maxBound = value maxBound

instance (Num a, SType' a) => Num (SExp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSymSoftware Add
    (-)         = sugarSymSoftware Sub
    (*)         = sugarSymSoftware Mul
    negate      = sugarSymSoftware Neg
    abs         = error "abs not implemeted for `SExp`"
    signum      = error "signum not implemented for `SExp`"

--------------------------------------------------------------------------------
-- * Instructions.
--------------------------------------------------------------------------------

desugar :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> SExp (Internal a)
desugar = SExp . Syntactic.desugar

sugar   :: (Syntactic a, Domain a ~ SoftwareDomain) => SExp (Internal a) -> a
sugar   = Syntactic.sugar . unSExp

resugar
  :: ( Syntactic a
     , Syntactic b
     , Internal a ~ Internal b
     , Domain a   ~ SoftwareDomain
     , Domain b   ~ SoftwareDomain
     )
  => a -> b
resugar = Syntactic.resugar

--------------------------------------------------------------------------------

-- Swap a `Imp.FreePred` constraint for software expressions to a `SoftwarePrimType` one.
withSType :: forall a b . Proxy a -> (Imp.FreePred SExp a => b) -> (SoftwarePrimType a => b)
withSType _ f = case softwareDict (softwareRep :: SoftwarePrimTypeRep a) of
  Dict -> f

-- Proves that a type from `SoftwarePrimTypeRep` satisfies `Imp.FreePred` for software expressions.
softwareDict :: SoftwarePrimTypeRep a -> Dict (Imp.FreePred SExp a)
softwareDict rep = case rep of
  BoolST   -> Dict
  Int8ST   -> Dict
  Word8ST  -> Dict
  FloatST  -> Dict

--------------------------------------------------------------------------------
-- ** General instructions.

instance References Software
  where
    type Reference Software = Ref

    initRef    = Software . fmap Ref . mapStructA (Imp.initRef) . resugar
    newRef     = Software . fmap Ref . mapStructA (const Imp.newRef) $ typeRep
    getRef     = Software . fmap resugar . mapStructA getRef' . unRef
    setRef ref = Software . sequence_ . zipListStruct setRef' (unRef ref) . resugar

-- Imp.getRef specialized a software constraint.
getRef' :: forall b . SoftwarePrimType b
  => Imp.Ref b
  -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
getRef' = withSType (Proxy :: Proxy b) Imp.getRef

-- Imp.setRef specialized to a software constraint.
setRef' :: forall b . SoftwarePrimType b
  => Imp.Ref b -> SExp b
  -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) ()
setRef' = withSType (Proxy :: Proxy b) Imp.setRef

--------------------------------------------------------------------------------
-- ** Software instructions.

--------------------------------------------------------------------------------
-- *** File handling.

-- | Open a file.
fopen :: FilePath -> IOMode -> Software Handle
fopen file = Software . Imp.fopen file

-- | Close a file.
fclose :: Handle -> Software ()
fclose = Software . Imp.fclose

-- | Check for end of file.
feof :: Handle -> Software (SExp Bool)
feof = Software . Imp.feof

-- | Put a primitive value to a handle.
fput :: (Formattable a, SType' a)
    => Handle
    -> String  -- Prefix
    -> SExp a  -- Expression to print
    -> String  -- Suffix
    -> Software ()
fput h pre e post = Software $ Imp.fput h pre e post

-- | Get a primitive value from a handle.
fget :: (Formattable a, SType' a) => Handle -> Software (SExp a)
fget = Software . Imp.fget

--------------------------------------------------------------------------------
-- *** Printing.

class PrintfType r
  where
    fprf :: Handle -> String -> [Imp.PrintfArg SExp] -> r

instance (a ~ ()) => PrintfType (Software a)
  where
    fprf h form = Software . Oper.singleInj . Imp.FPrintf h form . reverse

instance (Formattable a, SType' a, PrintfType r) => PrintfType (SExp a -> r)
  where
    fprf h form as = \a -> fprf h form (Imp.PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType r => Handle -> String -> r
fprintf h format = fprf h format []

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType r => String -> r
printf = fprintf Imp.stdout

--------------------------------------------------------------------------------
