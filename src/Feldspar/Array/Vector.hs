{-# language GADTs                  #-}
{-# language TypeFamilies           #-}
{-# language FlexibleInstances      #-}
{-# language FlexibleContexts       #-}
{-# language UndecidableInstances   #-}
{-# language MultiParamTypeClasses  #-}
{-# language FunctionalDependencies #-}

module Feldspar.Array.Vector where

import Feldspar
import Feldspar.Frontend (Arrays)
import Feldspar.Storable

import Prelude hiding (take, drop, length)

--------------------------------------------------------------------------------
-- * 1-dimensional vector library.
--------------------------------------------------------------------------------
--
-- This library has been inspired by the vector library in raw-feldspar
-- <https://github.com/Feldspar/raw-feldspar>
--
-- The general idea of pull and push vectors is described in
-- "Combining deep and shallow embedding of domain-specific languages"
-- <http://dx.doi.org/10.1016/j.cl.2015.07.003>.
--
-- Push arrays were originally introduced in
-- "Expressive array constructs in an embedded GPU kernel programming language"
-- <http://dx.doi.org/10.1145/2103736.2103740>.
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Manifest vectors.
--------------------------------------------------------------------------------

-- | A 1-dimensional vector with a concrete representation in memory
newtype Manifest m a = M { manifest :: Array m a }

--------------------------------------------------------------------------------
-- ** Pull vectors.
--------------------------------------------------------------------------------

-- | 1-dimensional pull vector: a vector representation that supports random
--   access and fusion of operations.
data Pull m a where
    Pull :: Expr m Length       -- ^ Length of vector.
         -> (Expr m Index -> a) -- ^ Index function.
         -> Pull m a

instance Functor (Pull m)
  where
    fmap f (Pull len ixf) = Pull len (f . ixf)

-- hmm...
instance (Expr m ~ e) => Indexed e (Pull m a)
  where
    type Elem (Pull m a) = a
    Pull _ ixf ! i = ixf i

instance (Expr m ~ e) => Slicable e (Pull m a)
  where
    slice from n = undefined -- todo: take n . drop from

instance (Expr m ~ e) => Finite e (Pull m a)
  where
    length (Pull len _) = len

-- | Data structures that are 'Pull'-like.
class    ( Indexed (Expr m) vec
         , Finite  (Expr m) vec
         , a ~ Elem vec)
        => Pully m vec a

instance ( Indexed (Expr m) vec
         , Finite  (Expr m) vec
         , a ~ Elem vec)
        => Pully m vec a

--------------------------------------------------------------------------------
-- *** Pully operations.
--------------------------------------------------------------------------------

-- | Convert a 'Pully' vector to 'Pull' vector.
toPull :: Pully m vec a => vec -> Pull m a
toPull vec = Pull (length vec) (vec!)
{-
-- | Take the head of a vector.
head :: Pully m vec a => vec -> a
head = (!0)
-}
-- | Drop the head of a vector.
tail :: (Pully m vec a, Num (Expr m Length)) => vec -> Pull m a
tail = drop 1

-- | Take the 'l' first elements of a vector.
take :: (Pully m vec a, Ord (Expr m Length)) => Expr m Length -> vec -> Pull m a
take l vec = Pull (min (length vec) l) (vec!)

-- | Drop the 'l' first elements of a vector.
drop :: (Pully m vec a, Num (Expr m Length)) => Expr m Length -> vec -> Pull m a
drop l vec = Pull (length vec - l) ((vec!) . (+l))

tails :: (Pully m vec a, Num (Expr m Length)) => vec -> Pull m (Pull m a)
tails vec = Pull (length vec + 1) (`drop` vec)

inits :: (Pully m vec a, Num (Expr m Length), Ord (Expr m Length)) => vec -> Pull m (Pull m a)
inits vec = Pull (length vec + 1) (`take` vec)

replicate :: Expr m Length -> a -> Pull m a
replicate l = Pull l . const

map :: Pully m vec a => (a -> b) -> vec -> Pull m b
map f vec = Pull (length vec) (f . (vec!))

zip :: Ord (Expr m Length) => (Pully m vec1 a, Pully m vec2 b) => vec1 -> vec2 -> Pull m (a, b)
zip a b = Pull (length a `min` length b) (\i -> (a!i, b!i))

-- | Back-permute a 'Pull' vector using an index mapping. The supplied mapping
--   must be a bijection when restricted to the domain of the vector. This
--   property is not checked, so use with care.
backPermute :: Pully m vec a
    => (Expr m Length -> Expr m Index -> Expr m Index) -> (vec -> Pull m a)
backPermute perm vec = Pull len ((vec!) . perm len)
  where
    len = length vec

reverse :: Num (Expr m Index) => Pully m vec a => vec -> Pull m a
reverse = backPermute $ \len i -> len-i-1

(...) :: Num (Expr m Index)
    => Expr m Index
    -> Expr m Index
    -> Pull m (Expr m Index)
l ... h = Pull (h-l+1) (+l)

infix 3 ...

--------------------------------------------------------------------------------
-- ** Push vectors.
--------------------------------------------------------------------------------

-- | 1-dimensional push vector: a vector representation that supports nested
--   write patterns and fusion of operations.
data Push m a
  where
    Push :: Expr m Length
         -> ((Expr m Index -> a -> m ()) -> m ())
         -> Push m a

instance Functor (Push m)
  where
    fmap f (Push len dump) = Push len $ \write ->
        dump $ \i -> write i . f

instance (Num (Expr m Length)) => Applicative (Push m)
  where
    pure a = Push 1 $ \write -> write 0 a
    vec1 <*> vec2 = Push (len1*len2) $ \write -> do
        dumpPush vec2 $ \i2 a ->
          dumpPush vec1 $ \i1 f ->
            write (i1*len2 + i2) (f a)
      where
        (len1,len2) = (length vec1, length vec2)

instance (Expr m ~ e) => Finite e (Push m a)
  where
    length (Push len _) = len

--------------------------------------------------------------------------------

-- | Vectors that can be converted to 'Push'
class Pushy m vec a | vec -> a
  where
    -- | Convert a vector to 'Push'
    toPush :: vec -> Push m a

instance Pushy m (Manifest m a) a
  where
    toPush = undefined -- todo: toPush . toPull . manifest

instance (m1 ~ m2) => Pushy m1 (Push m2 a) a
  where
    toPush = id

instance ( SyntaxM'  m (Expr m Length)
         , MonadComp m
         , Num                (Expr m Length)
         , Integral (Internal (Expr m Length)))
    => Pushy m (Pull m a) a
  where
    toPush vec = Push len $ \write ->
        for 0 (len-1) $ \i ->
          write i (vec!i)
      where
        len = length vec

-- | A version of 'toPush' that constrains the @m@ argument of 'Push' to that of
--   the monad in which the result is returned. This can be a convenient way to
--   avoid unresolved overloading.
toPushM :: (Pushy m vec a, Monad m) => vec -> m (Push m a)
toPushM = return . toPush

--------------------------------------------------------------------------------
-- *** Push operations.
--------------------------------------------------------------------------------

-- | Dump the contents of a 'Push' vector.
dumpPush
    :: Push m a                     -- ^ Vector to dump.
    -> (Expr m Index -> a -> m ())  -- ^ Function that writes one element.
    -> m ()
dumpPush (Push _ dump) = dump

-- | Append two vectors to make a 'Push' vector.
(++) :: (Pushy m vec1 a, Pushy m vec2 a, Num (Expr m Length), Monad m)
    => vec1
    -> vec2
    -> Push m a
vec1 ++ vec2 = Push (len1 + length v2) $ \write ->
    dumpPush v1 write >> dumpPush v2 (write . (+len1))
  where
    v1   = toPush vec1
    v2   = toPush vec2
    len1 = length v1

-- | Concatenate nested vectors to a 'Push' vector.
concat :: (Pushy m vec1 vec2, Pushy m vec2 a, Num (Expr m Length), MonadComp m)
    => Expr m Length  -- ^ Length of inner vectors.
    -> vec1           -- ^ Nested vector.
    -> Push m a
concat c vec = Push (len*c) $ \write ->
    dumpPush v $ \i row ->
      dumpPush row $ \j a ->
        write (i * length row + j) a
  where
    v   = fmap toPush $ toPush vec
    len = length v

-- | Forward-permute a 'Push' vector using an index mapping. The supplied
--   mapping must be a bijection when restricted to the domain of the vector.
--   This property is not checked, so use with care.
forwardPermute :: Pushy m vec a =>
    (Expr m Length -> Expr m Index -> Expr m Index) -> vec -> Push m a
forwardPermute p vec = Push len $ \write ->
    dumpPush v $ \i a ->
      write (p len i) a
  where
    v   = toPush vec
    len = length v

--------------------------------------------------------------------------------
-- * Writing to memory.
--------------------------------------------------------------------------------

class ViewManifest m vec a | vec -> a
  where
    -- | Try to cast a vector to 'Manifest' directly
    viewManifest :: vec -> Maybe (Manifest m a)
    viewManifest _ = Nothing

instance ViewManifest m (Pull m a) a
instance ViewManifest m (Push m a) a
instance ViewManifest m (Manifest m a) a
  where
    viewManifest = Just



--------------------------------------------------------------------------------
