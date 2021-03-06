{-# language TypeFamilies          #-}
{-# language FlexibleInstances     #-}
{-# language MultiParamTypeClasses #-}
{-# language ScopedTypeVariables   #-}

module Feldspar.Storable where

import Feldspar.Frontend
import Data.Struct

import Data.Proxy

--------------------------------------------------------------------------------
-- * Storable.
--------------------------------------------------------------------------------

class Storable m a
  where
    -- | Memory representation
    type StoreRep m a
    -- | Size of memory representation
    type StoreSize m a

    -- | Creat a fresh memory store. It is usually better to use 'newStore'
    --   instead of this function as it improves type inference.
    newStoreRep :: MonadComp m => proxy a -> StoreSize m a -> m (StoreRep m a)

    -- | Store a value to a fresh memory store. It is usually better to use
    --   'initStore' instead of this function as it improves type inference.
    initStoreRep :: MonadComp m => a -> m (StoreRep m a)

    -- | Read from a memory store. It is usually better to use 'readStore'
    --   instead of this function as it improves type inference.
    readStoreRep :: MonadComp m => StoreRep m a -> m a

    -- | Unsafe freezing of a memory store. It is usually better to use
    --   'unsafeFreezeStore' instead of this function as it improves type
    --   inference.
    unsafeFreezeStoreRep :: MonadComp m => StoreRep m a -> m a

    -- | Write to a memory store. It is usually better to use 'writeStore'
    --   instead of this function as it improves type inference.
    writeStoreRep :: MonadComp m => StoreRep m a -> a -> m ()

instance Storable m ()
  where
    type StoreRep m ()  = ()
    type StoreSize m () = ()
    newStoreRep _ _        = return ()
    initStoreRep _         = return ()
    readStoreRep _         = return ()
    unsafeFreezeStoreRep _ = return ()
    writeStoreRep _ _      = return ()

instance forall m a b . (Storable m a, Storable m b) => Storable m (a,b)
  where
    type StoreRep m (a,b) = (StoreRep m a, StoreRep m b)
    type StoreSize m (a,b) = (StoreSize m a, StoreSize m b)
    newStoreRep _ (a,b)          = (,) <$> newStoreRep (Proxy :: Proxy a) a <*> newStoreRep (Proxy :: Proxy b) b
    initStoreRep (a,b)           = (,) <$> initStoreRep a <*> initStoreRep b
    readStoreRep (la,lb)         = (,) <$> readStoreRep la <*> readStoreRep lb
    unsafeFreezeStoreRep (la,lb) = (,) <$> unsafeFreezeStoreRep la <*> unsafeFreezeStoreRep lb
    writeStoreRep (la,lb) (a,b)  = writeStoreRep la a >> writeStoreRep lb b

--------------------------------------------------------------------------------
-- ** User interface.
--------------------------------------------------------------------------------

-- | Memory for storing values.
newtype Store m a = Store { unStore :: StoreRep m a }

-- | Create a fresh 'Store'.
newStore :: forall a m . (MonadComp m, Storable m a)
  => StoreSize m a
  -> m (Store m a)
newStore = fmap Store . newStoreRep (Proxy :: Proxy a)

-- | Store a value to a fresh 'Store'.
initStore :: (MonadComp m, Storable m a) => a -> m (Store m a)
initStore = fmap Store . initStoreRep

-- | Read from a 'Store'.
readStore :: (MonadComp m, Storable m a) => Store m a -> m a
readStore = readStoreRep . unStore

-- | Write to a 'Store'.
writeStore :: (MonadComp m, Storable m a) => Store m a -> a -> m ()
writeStore = writeStoreRep . unStore

-- | Unsafe freezeing of a 'Store'. This operation is only safe if the 'Store'
--   is not updated as long as the returned value is alive.
unsafeFreezeStore :: (MonadComp m, Storable m a) => Store m a -> m a
unsafeFreezeStore = unsafeFreezeStoreRep . unStore

-- | Update a 'Store' in-place, that is, a update that won't produce any
--   temporary variable to store values read from the 'Store'.
inplace :: (MonadComp m, Storable m a) => Store m a -> (a -> a) -> m ()
inplace store f = writeStore store . f =<< unsafeFreezeStore store

--------------------------------------------------------------------------------
