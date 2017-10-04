module Vectors where

import Feldspar
import Feldspar.Array.Vector

import Feldspar.Software
import Feldspar.Software as Soft (icompile)

import Feldspar.Hardware
import Feldspar.Hardware as Hard (icompileWrap)

import Prelude hiding (take, drop, reverse, length, zip, zipWith, sum)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- pull vector short-hands.
type SPull = Pull Software
type HPull = Pull Hardware

-- push vector short-hands.
type SPush = Push Software
type HPush = Push Hardware

--------------------------------------------------------------------------------

sumLast5 :: SPull (SExp Word32) -> SExp Word32
sumLast5 = sum . take 5 . reverse

--------------------------------------------------------------------------------

ex1 :: IO ()
ex1 = scomp (sumLast5 inp)
  where
    inp :: SPull (SExp Word32)
    inp = 0 ... 10

scomp :: SExp Word32 -> IO ()
scomp e = Soft.icompile (printf "%d" e)

--------------------------------------------------------------------------------
