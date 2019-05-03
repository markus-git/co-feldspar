{-# language GADTs #-}
{-# language Rank2Types #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Array.Queue where

import Feldspar
import Feldspar.Frontend (Arrays)
import Feldspar.Array.Vector

import Prelude hiding (length, mod, reverse, drop, take, (++))

--------------------------------------------------------------------------------
-- * Queues.
--------------------------------------------------------------------------------

data Queue m a = Queue
  { queue_get  :: Expr m Index -> m a
  , queue_put  :: a -> m ()
  , queue_with :: forall b . SyntaxM m b => (Pull (Expr m) a -> m b) -> m b
  }

type Queues m a =
  ( Finite  (Expr m) (Array m a)
  , Finite  (Expr m) (IArray m a)
  , Indexed (Expr m) (IArray m a)
  , ArrElem (IArray m a) ~ a

  , Multiplicative (Expr m)
  , Vector (Expr m)
  
  , SyntaxM m (Expr m Index)
  , SyntaxM m (Expr m Length)
  , PredOf (Expr m) Length
  )

--------------------------------------------------------------------------------

queueBuffer :: forall m a . (MonadComp m, SyntaxM m a, Queues m a)
  => Array m a -> m (Queue m a)
queueBuffer buf =
  do ir <- initRef (0 :: Expr m Index)
     let get :: Expr m Index -> m a
         get j = do
           i <- unsafeFreezeRef ir
           getArr buf $ safeIndex i j
     let put :: a -> m ()
         put a = do
           i <- unsafeFreezeRef ir
           setArr buf i a
           setRef ir ((i+1) `mod` len)
     let with :: forall b . (SyntaxM m b) => (Pull (Expr m) a -> m b) -> m b
         with f = do
           i <- unsafeFreezeRef ir
           v <- unsafeFreezeArr buf
           f $ backPermute (\_ -> safeIndex i) v
     return $ Queue { queue_get = get, queue_put = put, queue_with = with }
  where
    len = length buf
    safeIndex i j = (len + i - j - 1) `mod` len

queueVector ::
  ( Manifestable m vec a
  , Finite (Expr m) vec
  , SyntaxM m a
  , MonadComp m
  , Queues m a
  )
  => vec -> m (Queue m a)
queueVector v =
  do buf <- newArr $ length v
     manifestStore buf v
     queueBuffer buf

newQueue :: (SyntaxM m a, MonadComp m, Queues m a)
  => Expr m Length -> m (Queue m a)
newQueue l = newArr l >>= queueBuffer

--------------------------------------------------------------------------------

queueDoubleBuffer :: forall m a . (MonadComp m, SyntaxM m a, Queues m a)
  => Expr m Length -> Array m a -> m (Queue m a)
queueDoubleBuffer len buf =
  do ir <- initRef (0 :: Expr m Index)
     let get :: Expr m Index -> m a
         get j = do
           i <- unsafeFreezeRef ir
           getArr buf $ len + i - j - 1
     let put :: a -> m ()
         put a = do
           i <- unsafeFreezeRef ir
           setArr buf i a
           setArr buf (i + len) a
           setRef ir ((i + 1) `mod` len)
     let with :: forall b . (SyntaxM m b) => (Pull (Expr m) a -> m b) -> m b
         with f = do
           i <- unsafeFreezeRef ir
           v <- unsafeFreezeArr buf
           f $ reverse $ take len $ drop i v
     return $ Queue { queue_get = get, queue_put = put, queue_with = with }

queueDoubleVector :: forall m vec a .
  ( Manifestable m vec a
  , Finite (Expr m) vec
  , Slicable (Expr m) (IArray m a)
  , Pushy m vec a
  , SyntaxM m a
  , MonadComp m
  , Loop m
  , Queues m a
  )
  => vec -> m (Queue m a)
queueDoubleVector v =
  do let len = length v
     buf <- newArr $ 2 * len
     manifestStore buf $ (v ++ v :: Push m a)
     queueDoubleBuffer len buf

newDoubleQueue :: (SyntaxM m a, MonadComp m, Queues m a)
  => Expr m Length -> m (Queue m a)
newDoubleQueue l =
  do buf <- newArr $ 2 * l
     queueDoubleBuffer l buf
  
--------------------------------------------------------------------------------
