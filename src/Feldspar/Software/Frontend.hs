{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language Rank2Types #-}

{-# language InstanceSigs #-}
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
import Language.Syntactic.Functional

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- syntactic.
import Language.Syntactic

--------------------------------------------------------------------------------
-- * Software ...
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Expressions.

instance Value SoftwareDomain
  where
    value = sugarSymSoftware . Lit

instance Share SoftwareDomain
  where
    share = sugarSymSoftware (Let "")

instance Boolean SoftwareDomain
  where
    bool t f b = sugarSymSoftware Cond b t f
    false = value False
    true  = value True

--------------------------------------------------------------------------------
-- ** Instructions.
{-
-- ...
withSType :: forall a b . Proxy a -> (Imp.FreePred SExp a => b) -> (SoftwarePrimType a => b)
withSType _ f = case softwareDict (softwareRep :: SoftwarePrimTypeRep a) of
  Dict -> f

-- ...
softwareDict :: SoftwarePrimTypeRep a -> Dict (Imp.FreePred SExp a)
softwareDict rep = case rep of
  BoolST   -> Dict
  Int8ST   -> Dict
  Word8ST  -> Dict
  FloatST  -> Dict

-}
--------------------------------------------------------------------------------
-- *** ... comp instr ...
{-
instance References Software
  where
    type Reference Software = Ref

    initRef :: forall a . SType a => a -> Software (Ref a)
    initRef
        = liftComp
        . fmap Ref
        . mapStructA (Imp.initRef)
        . construct

    newRef :: forall a . SType a => Software (Ref a)
    newRef
        = liftComp
        . fmap Ref
        . mapStructA (const Imp.newRef)
        $ (typeRep :: STypeRep (Internal a))

    getRef :: SType a => Ref a -> Software a
    getRef
        = liftComp
        . fmap destruct
        . mapStructA getty
        . unRef
      where
        getty :: forall b . SoftwarePrimType b => Imp.Ref b -> Prog SExp SoftwarePrimType (SExp b)
        getty = withSType (Proxy :: Proxy b) Imp.getRef

    setRef :: SType a => Ref a -> a -> Software ()
    setRef ref
        = liftComp
        . sequence_
        . zipListStruct setty (unRef ref)
        . construct
      where
        setty :: forall b . SoftwarePrimType b => Imp.Ref b -> SExp b -> Prog SExp SoftwarePrimType ()
        setty = withSType (Proxy :: Proxy b) Imp.setRef
-}
--------------------------------------------------------------------------------
-- *** File handling.
{-
-- | Open a file
fopen :: FilePath -> IOMode -> Software Handle
fopen file = Software . Imp.fopen file

-- | Close a file
fclose :: Handle -> Software ()
fclose = Software . Imp.fclose

-- | Check for end of file
feof :: Handle -> Software (SExp Bool)
feof = Software . Imp.feof

-- | Put a primitive value to a handle
fput :: (Formattable a, SoftwareType a)
    => Handle
    -> String  -- Prefix
    -> SExp a  -- Expression to print
    -> String  -- Suffix
    -> Software ()
fput h pre e post = Software $ Imp.fput h pre e post

-- | Get a primitive value from a handle
fget :: (Formattable a, SoftwareType a) => Handle -> Software (SExp a)
fget = Software . Imp.fget
-}
--------------------------------------------------------------------------------
-- *** Printing.
{-
class PrintfType r
  where
    fprf :: Handle -> String -> [Imp.PrintfArg SExp] -> r

instance (a ~ ()) => PrintfType (Software a)
  where
    fprf h form = Software . Oper.singleInj . Imp.FPrintf h form . reverse

instance (Formattable a, SoftwareType a, PrintfType r) => PrintfType (SExp a -> r)
  where
    fprf h form as = \a -> fprf h form (Imp.PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType r => Handle -> String -> r
fprintf h format = fprf h format []

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType r => String -> r
printf = fprintf Imp.stdout
-}
--------------------------------------------------------------------------------
