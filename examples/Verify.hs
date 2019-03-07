module Verify where

import Feldspar.Software
import Feldspar.Software.Verify

--------------------------------------------------------------------------------

summer :: Software ()
summer = do
  sum  <- initRef (0 :: SExp Word32)
  for 0 10 $ \ix -> do
    tmp <- getRef sum
    setRef sum (tmp + ix)

--------------------------------------------------------------------------------
