{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}

module Feldspar.Software.Frontend where

import Feldspar.Representation
import Feldspar.Frontend

import Feldspar.Software.Primitive
import Feldspar.Software.Representation

import Data.Struct

import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- syntactic.
import Language.Syntactic

--------------------------------------------------------------------------------
-- * Software expressions.
--------------------------------------------------------------------------------

instance VAL SoftwarePrimType SoftwareDomain
  where
    value = sugarSymPrimSoftware . Lit

{-
value :: (Syntax a, Domain a ~ SoftwareDomain, SoftwarePrimType (Internal a)) => Internal a -> a
value = sugarSymPrimSoftware . Lit
-}
--------------------------------------------------------------------------------

instance NUM SoftwarePrimType Data
  where
    plus    = sugarSymPrimSoftware Add
--    minus   = sugarSymSoftware Sub
--    times   = sugarSymSoftware Mul
--    negate  = sugarSymSoftware Neg

--------------------------------------------------------------------------------
-- * Software instructions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * File handling.

-- | Open a file
fopen :: FilePath -> IOMode -> Software Handle
fopen file = Software . Imp.fopen file

-- | Close a file
fclose :: Handle -> Software ()
fclose = Software . Imp.fclose

-- | Check for end of file
feof :: Handle -> Software (Data Bool)
feof = Software . Imp.feof

-- | Put a primitive value to a handle
fput :: (Formattable a, SoftwareType a)
    => Handle
    -> String  -- Prefix
    -> Data a  -- Expression to print
    -> String  -- Suffix
    -> Software ()
fput h pre e post = Software $ Imp.fput h pre e post

-- | Get a primitive value from a handle
fget :: (Formattable a, SoftwareType a) => Handle -> Software (Data a)
fget = Software . Imp.fget

--------------------------------------------------------------------------------
-- * Printing.

class PrintfType r
  where
    fprf :: Handle -> String -> [Imp.PrintfArg Data] -> r

instance (a ~ ()) => PrintfType (Software a)
  where
    fprf h form = Software . Oper.singleInj . Imp.FPrintf h form . reverse

instance (Formattable a, SoftwareType a, PrintfType r) => PrintfType (Data a -> r)
  where
    fprf h form as = \a -> fprf h form (Imp.PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType r => Handle -> String -> r
fprintf h format = fprf h format []

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType r => String -> r
printf = fprintf Imp.stdout

--------------------------------------------------------------------------------
