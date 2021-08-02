{-# language ScopedTypeVariables #-}

module Tut1_HelloWorld where

import Feldspar
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

-- hmm...
import Language.Embedded.Hardware.Command (Mode(..))


--------------------------------------------------------------------------------
-- * Hello World! (Software).
--------------------------------------------------------------------------------

-- \Hello world\ program that runs in the `Software` monad.
helloWorld :: Software ()
helloWorld = printf "Hello world!\n"

--------------------------------------------------------------------------------

-- Generate C code, call the C compiler, and then run the resulting executable:
test1 = Soft.runCompiled helloWorld

--  Run directly in Haskell, without ever generating C code:
test2 = Soft.runIO helloWorld

-- Compile to C code and show the generated code:
test3 = putStrLn $ Soft.compile helloWorld

-- Same as above, but shorter:
test4 = Soft.icompile helloWorld

-- Compare output written to \stdout\ from a Co-Feldspar program with that of a
-- reference Haskell `IO` program. The final, empty string argument will be fed
-- into both the Co-Feldspar and Haskell programs.
test5 = Soft.compareCompiled helloWorld (putStrLn "Hello world!") ""

-- Same as above, but we obtain the Haskell reference through `runIO` instead.
test6 = Soft.compareCompiled helloWorld (runIO helloWorld) ""

-- Run all tests so far in order.
testAll =
  do test1
     test2
     test3
     test4
     test5
     test6

--------------------------------------------------------------------------------
-- * Adder (Hardware).
--------------------------------------------------------------------------------

-- A simple adder impl. for 'Hardware' expressions.
adder :: HExp Int32 -> HExp Int32 -> HExp Int32
adder a b = a + b

-- Program running in the 'Hardware' monad and using 'adder' with local
-- signals/variables.
adder_wrap :: Hardware ()
adder_wrap =
  do a <- initSignal 5
     b <- initSignal 10
     c <- newSignal
     -- Here we could safely swap getSignal out for unsafeFreezeSignal to get
     -- rid of the extra (but harmless) variable reads of 'a' and 'b'.
     va <- getSignal a 
     vb <- getSignal b
     setSignal c (adder va vb)

test7 = Hard.icompile adder_wrap

-- Another program running in the 'Hardware' monad using 'adder' with
-- input/output signals (put into either a component decl. or an AXI4-lite
-- wrapper by the two compiler calls below).
adder_hsig :: HSig (Signal Int32 -> Signal Int32 -> Signal Int32 -> ())
adder_hsig =
  input $ \a ->
  input $ \b ->
  retExpr $ adder a b

test8 = Hard.icompileSig adder_hsig

test9 = Hard.icompileAXILite adder_hsig

--------------------------------------------------------------------------------
