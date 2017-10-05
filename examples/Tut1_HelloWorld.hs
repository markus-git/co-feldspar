module Tut1_HelloWorld where

import Feldspar
import Feldspar.Software

--------------------------------------------------------------------------------
-- * Hello World!
--------------------------------------------------------------------------------

-- \Hello World\ program that runs in the 'Software' monad.
helloWorld :: Software ()
helloWorld = printf "Hello world!\n"

--------------------------------------------------------------------------------

-- Generate C code, call the C compiler, and then run the resulting executable:
test1 = runCompiled helloWorld

--  Run directly in Haskell, without ever generating C code:
test2 = runIO helloWorld

-- Compile to C code and show the generated code:
test3 = putStrLn $ compile helloWorld

-- Same as above, but shorter:
test4 = icompile helloWorld

-- Compare output written to \stdout\ from a Co-Feldspar program with that of a
-- reference Haskell 'IO' program. The final, empty string argument will be fed
-- into both the Co-Feldspar and Haskell programs.
test5 = compareCompiled helloWorld (putStrLn "Hello world!") ""

-- Same as above, but we obtain the Haskell reference through 'runIO' instead.
test6 = compareCompiled helloWorld (runIO helloWorld) ""

--------------------------------------------------------------------------------

testAll =
  do test1
     test2
     test3
     test4
     test5
     test6

--------------------------------------------------------------------------------
