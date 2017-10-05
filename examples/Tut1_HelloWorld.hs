{-# language ScopedTypeVariables #-}

module Tut1_HelloWorld where

import Feldspar
import Feldspar.Software as Soft
import Feldspar.Hardware as Hard

-- hmm...
import Language.Embedded.Hardware.Command (Mode(..))

--------------------------------------------------------------------------------
-- * Hello World! (Software)
--------------------------------------------------------------------------------

-- \Hello world\ program that runs in the 'Software' monad.
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
-- reference Haskell 'IO' program. The final, empty string argument will be fed
-- into both the Co-Feldspar and Haskell programs.
test5 = Soft.compareCompiled helloWorld (putStrLn "Hello world!") ""

-- Same as above, but we obtain the Haskell reference through 'runIO' instead.
test6 = Soft.compareCompiled helloWorld (runIO helloWorld) ""


--------------------------------------------------------------------------------

testAll =
  do test1
     test2
     test3
     test4
     test5
     test6


--------------------------------------------------------------------------------
-- * Adder (Hardware)
--------------------------------------------------------------------------------

-- A simple adder that runs in the 'Hardware' monad.
adder :: Signal Int32 -> Signal Int32 -> Signal Int32 -> Hardware ()
adder a b c =
  do va <- getSignal a
     vb <- getSignal b
     setSignal c (va + vb)

-- Explicit entity/architecture wrapper.
component :: Hardware ()
component =
  do (a, b, c) <- entity "a" $ do
       a :: Signal Int32 <- newPort In
       b :: Signal Int32 <- newPort In
       c :: Signal Int32 <- newPort Out
       return (a, b, c)

     architecture "a" "behav" $ do
       process (a .: b .: []) $ do
         adder a b c

--------------------------------------------------------------------------------

-- Compile to VHDL and show the generated design:
test7 = putStrLn $ Hard.compile component

-- Same as above, but shorter:
test8 = Hard.icompile component

-- If we don't care about wires, we can wrap our designs in an empty entity and
-- use local signals instead (useful for inspecting an unfinished design).
test9 = Hard.icompileWrap $
  do a <- newSignal
     b <- newSignal
     c <- newSignal
     adder a b c

--------------------------------------------------------------------------------
