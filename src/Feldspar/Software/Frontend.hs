{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}

module Feldspar.Software.Frontend where

import Feldspar.Primitive
import Feldspar.Frontend

import Feldspar.Software.Primitive
import Feldspar.Software.Representation

import Data.Struct

import Control.Monad.Trans

import qualified Control.Monad.Operational.Higher as Oper

import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

instance NUM Data where
  plus   = sugarSymSoft Add
  minus  = sugarSymSoft Sub
  times  = sugarSymSoft Mul
  negate = sugarSymSoft Neg

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

instance MonadComp Software
  where
    type Expr Software = Data
    type Pred Software = SoftwarePrimType

    liftComp = Software . lift

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
