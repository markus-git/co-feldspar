-- | Inhabited types
module Data.Inhabited where

import Data.Int
import Data.Word

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

class Inhabited a
  where
    example :: a

--------------------------------------------------------------------------------

instance Inhabited Bool   where example = False
instance Inhabited Int8   where example = 0
instance Inhabited Int16  where example = 0
instance Inhabited Int32  where example = 0
instance Inhabited Int64  where example = 0
instance Inhabited Word8  where example = 0                               
instance Inhabited Word16 where example = 0                               
instance Inhabited Word32 where example = 0                               
instance Inhabited Word64 where example = 0                               
instance Inhabited Float  where example = 0
instance Inhabited Double where example = 0

--------------------------------------------------------------------------------

instance (Inhabited a, Inhabited b) => Inhabited (a, b)
  where
    example = (example, example)

--------------------------------------------------------------------------------
