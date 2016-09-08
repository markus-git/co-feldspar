module Basic where

import Feldspar.Software

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

basic :: Software ()
basic = do
  let zero = 0 :: Data Int8
      one  = 1 :: Data Int8
      
  a <- initRef zero
  u <- getRef a
  setRef a (u `plus` one)

--------------------------------------------------------------------------------
