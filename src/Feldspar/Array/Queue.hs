{-# language GADTs #-}
{-# language Rank2Types #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Array.Queue where

import Feldspar
import Feldspar.Frontend (Arrays)
import Feldspar.Array.Vector

import Prelude hiding (length, mod)

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
  , Num (Expr m Index)
  
  , SyntaxM m (Expr m Index)
  , SyntaxM m (Expr m Length)
  , PredOf (Expr m) Length
  )

--------------------------------------------------------------------------------

initQueueFromBuffer :: forall m a .
     ( MonadComp m
     , SyntaxM m a
     , Queues m a
     )
  => Array m a -> m (Queue m a)
initQueueFromBuffer buf =
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
         with :: forall b . (SyntaxM m b) => (Pull (Expr m) a -> m b) -> m b
         with f = do
           i <- unsafeFreezeRef ir
           v <- unsafeFreezeArr buf
           f $ backPermute (\_ -> safeIndex i) v
     return $ Queue { queue_get = get, queue_put = put, queue_with = with }
  where
    len = length buf
    safeIndex i j = (len + i - j - 1) `mod` len

initQueue ::
  ( Manifestable m vec a
  , Finite (Expr m) vec
  , SyntaxM m a
  , MonadComp m
  , Queues m a
  )
  => vec -> m (Queue m a)
initQueue v =
  do buf <- newArr $ length v
     manifestStore buf v
     initQueueFromBuffer buf

newQueue :: (SyntaxM m a, MonadComp m, Queues m a)
  => Expr m Length -> m (Queue m a)
newQueue l = newArr l >>= initQueueFromBuffer

--------------------------------------------------------------------------------
