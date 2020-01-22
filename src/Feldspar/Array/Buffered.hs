{-# language TypeFamilies     #-}
{-# language FlexibleContexts #-}
{-# language RecordWildCards  #-}
{-# language MultiParamTypeClasses #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Array.Buffered where

import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Array.Vector

import Prelude hiding (length)
import qualified Prelude as P

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | Double-buffered storage.
data Store m a = Store
    { activeBuf :: Array m a
    , freeBuf   :: Array m a
    }

--------------------------------------------------------------------------------

class ArraysEq vec1 vec2
  where
    unsafeArrEq :: vec1 a -> vec2 a -> Bool

class Arrays m => ArraysSwap m
  where
    unsafeArrSwap :: Array m a -> Array m a -> m ()

--------------------------------------------------------------------------------

-- | Create a new double-buffered 'Store', initialized to a 0x0 matrix.
newStore :: (SyntaxM m a, MonadComp m) => Expr m Length -> m (Store m a)
newStore l = Store <$> newArr l <*> newArr l

-- | Create a new 'Store' from a single array.
newInPlaceStore
  :: ( SyntaxM m a
     , MonadComp m
     , Finite (Expr m) (IArray m a)
     , Finite (Expr m) (Array m a)
     )
  => Expr m Length -> m (Store m a)
newInPlaceStore l = do
  arr <- newArr l
  brr <- unsafeFreezeArr arr >>= unsafeThawArr
  return (Store arr brr)

-- | Read the contents of a 'Store' without making a copy. This is generally
--   only safe if the the 'Store' is not updated as long as the resulting vector
--   is alive.
unsafeFreezeStore
  :: ( SyntaxM m a
     , MonadComp m
     , Finite   (Expr m) (Array  m a)
     , Slicable (Expr m) (IArray m a)
     , Num (Expr m Index)
     )
  => Expr m Length -> Store m a -> m (Manifest m a)
unsafeFreezeStore l st = M <$> unsafeFreezeSlice l (activeBuf st)

-- | Cheap swapping of the two buffers in a 'Store'.
swapStore
  :: ( SyntaxM    m a
     -- hmm..
     , ArraysSwap m
     )
  => Store m a -> m ()
swapStore Store {..} = unsafeArrSwap activeBuf freeBuf

replaceFreeStore :: (SyntaxM m a, Arrays m) => Expr m Length -> Store m a -> m (Store m a)
replaceFreeStore l Store {..} = Store activeBuf <$> newArr l

-- | Write a vector to a 'Store'. The operation may become a no-op
--   if the vector is already in the 'Store'.
setStore
  :: forall m a vec .
     ( Manifestable m vec a
     , Finite (Expr m) vec
     , SyntaxM m a
     --
     , ArraysSwap m
     , ArraysEq (Array m) (IArray m)
     )
  => Store m a -> vec -> m ()
setStore st@Store {..} vec = case viewManifest vec of
    Just (M iarr :: Manifest m a) | unsafeArrEq activeBuf iarr
      -> return ()
    _ -> manifestStore freeBuf vec >> swapStore st
-- todo: Should check for offset and length differences as well.

-- | Write the contents of a vector to a 'Store' and get it back as a
--   'Manifest' vector.
store
  :: ( Manifestable m vec a
     , Finite (Expr m) vec
     , SyntaxM m a
     , MonadComp m
     --
     , Finite   (Expr m) (Array  m a)
     , Slicable (Expr m) (IArray m a)
     , Num (Expr m Index)
     --
     , ArraysSwap m
     , ArraysEq (Array m) (IArray m)
     )
  => Store m a -> vec -> m (Manifest m a)
store st vec = setStore st vec >> unsafeFreezeStore (length vec) st

loopStore
  :: ( Manifestable m vec1 a
     , Finite (Expr m) vec1
     , Manifestable m vec2 a
     , Finite (Expr m) vec2
     , SyntaxM m a
     , MonadComp m
     , Loop m
     --
     , Integral i
     , SyntaxM' m (Expr m i)
     , SyntaxM' m (Expr m Length)
     --
     , Finite   (Expr m) (Array  m a)
     , Slicable (Expr m) (IArray m a)
     , Num (Expr m Index)
     --
     , ArraysSwap m
     , ArraysEq (Array m) (IArray m)
     )
  => Store m a
  -> Expr m i  -- ^ Lower bound.
  -> Int       -- ^ Step.
  -> Expr m i  -- ^ Upper bound.
  -> (Expr m i -> Manifest m a -> m vec1)
  -> vec2
  -> m (Manifest m a)
loopStore store low step high body init = do
  setStore store init
  ilen <- initRef $ length init
  for low step high $ \ix -> do
    len  <- unsafeFreezeRef ilen
    next <- body ix =<< unsafeFreezeStore len store
    setStore store next
    setRef ilen $ length next
  len <- unsafeFreezeRef ilen
  unsafeFreezeStore len store

--------------------------------------------------------------------------------
