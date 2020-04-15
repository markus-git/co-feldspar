{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE QuasiQuotes #-}

module Vectors where

import Feldspar
import Feldspar.Array.Vector
import Feldspar.Array.Buffered

import Feldspar.Software
import Feldspar.Software as Soft (icompile)
import Feldspar.Software.Compile

import Feldspar.Software.Marshal

import Feldspar.Hardware hiding (Arr, IArr, Ref)
import Feldspar.Hardware as Hard (icompile, icompileSig, icompileAXILite)

import Control.Monad (void)
import Data.Complex (Complex)

-- language-c-quote
import Language.C.Quote.GCC
import qualified Language.C.Syntax as C

-- imperative-edsl
import qualified Language.Embedded.Backend.C  as Imp

import Prelude hiding (take, drop, reverse, length, zip, zipWith, sum, tail, map)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

sumLast5 :: SPull (SExp Word32) -> SExp Word32
sumLast5 = sum . take 5 . reverse

--------------------------------------------------------------------------------

test1 :: IO ()
test1 = Soft.icompile $ printf "%d" $ sumLast5 inp
  where
    inp :: SPull (SExp Word32)
    inp = 0 ... 10

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

dot :: (Vector exp, Pully exp vec a, Num a, Syntax exp a) => vec -> vec -> a
dot a b = sum $ zipWith (*) a b

dotArr :: IArr (SExp Int32) -> IArr (SExp Int32) -> SExp Int32
dotArr = dot

dotProg :: Software ()
dotProg = connectStdIO $ return . uncurry dotArr

dotIO :: IO ()
dotIO = Soft.icompile dotProg

--------------------------------------------------------------------------------

fir :: (Vector exp, Num a, Syntax exp a) => Pull exp a -> Pull exp a -> Pull exp a
fir coeff = map (dot coeff . reverse) . tail . inits

firArr :: IArr (SExp Int32) -> IArr (SExp Int32) -> Pull SExp (SExp Int32)
firArr a b = fir (toPull a) (toPull b)

firProg :: Software ()
firProg = connectStdIO $ manifestFresh . uncurry firArr

firIO :: IO ()
firIO = Soft.icompile firProg

--------------------------------------------------------------------------------

type SStore  a = Store  Software a

printTime_def = [cedecl|
void printTime(typename clock_t start, typename clock_t end)
{
  printf("CPU time (sec): %f\n", (double)(end-start) / CLOCKS_PER_SEC);
}
|]

sizeOf_double_complex :: SExp Length
sizeOf_double_complex = 16

-- | Measure the time for 100 runs of 'fftCore' (excluding initialization) for
-- arrays of the given size
benchmark :: SExp Length -> Software ()
benchmark n = do
  addInclude "<stdio.h>"
  addInclude "<string.h>"
  addInclude "<time.h>"
  addDefinition printTime_def
  start <- newObject "clock_t" False
  end   <- newObject "clock_t" False
  st1 :: SStore (SExp (Complex Double)) <- newStore n
  inp1 <- unsafeFreezeStore n st1
  callProc "memset"
      [ iarrArg (manifest inp1)
      , valArg (0 :: SExp Index)
      , valArg (n*sizeOf_double_complex)
      ]
  st2 :: SStore (SExp (Complex Double)) <- newStore n
  inp2 <- unsafeFreezeStore n st2
  callProc "memset"
      [ iarrArg (manifest inp1)
      , valArg (0 :: SExp Index)
      , valArg (n*sizeOf_double_complex)
      ]  
  callProcAssign start "clock" []

  for 0 1 99 $ \(_ :: SExp Index) ->
    void $ manifestFresh (fir (toPull inp1) (toPull inp2))

  callProcAssign end "clock" []
  callProc "printTime" [objArg start, objArg end]

runBenchmark n = runCompiled'
  (Imp.def :: CompilerOpts)
  (Imp.def {Imp.externalFlagsPre = ["-O3"], Imp.externalFlagsPost = ["-lm"]})
  (benchmark n)

printBenchmark n = Soft.icompile (benchmark n)

--------------------------------------------------------------------------------

dot_sig :: HSig (SArr Word32 -> SArr Word32 -> Signal Word32 -> ())
dot_sig =
  inputIArr 1 $ \a ->
  inputIArr 1 $ \b ->
  ret $ pure $ dot a b
  -- `dot` is pure, so we lift its result.

test3 :: IO ()
test3 = Hard.icompileSig $ dot_sig
  -- Seems the optimizer isn't happy, might be just my installation tho.

test4 :: IO ()
test4 = Hard.icompileAXILite $ dot_sig

--------------------------------------------------------------------------------

dot_mmap :: Software ()
dot_mmap =
  do dot <- mmap "0x43C00000" dot_sig
     a :: Arr (SExp Word32) <- initArr [1]
     b :: Arr (SExp Word32) <- initArr [1]
     c :: Ref (SExp Word32) <- newRef
     --
     call dot (a >>: b >>: c >: nil)
     --
     result <- getRef c
     printf "dot: %d\n" result

test5 :: IO ()
test5 = Soft.icompile dot_mmap

--------------------------------------------------------------------------------
