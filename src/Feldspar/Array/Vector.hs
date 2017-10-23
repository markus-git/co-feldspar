{-# language GADTs                  #-}
{-# language TypeFamilies           #-}
{-# language FlexibleInstances      #-}
{-# language FlexibleContexts       #-}
{-# language UndecidableInstances   #-}
{-# language MultiParamTypeClasses  #-}
{-# language FunctionalDependencies #-}
{-# language DefaultSignatures      #-}

{-# language ScopedTypeVariables    #-}
{-# language ConstraintKinds        #-}

module Feldspar.Array.Vector where

import Feldspar
import Feldspar.Frontend (Arrays)
import Feldspar.Storable

import Data.List (genericLength)

import Control.Monad ((<=<), void)

import Prelude hiding (take, drop, reverse, length, zip, zipWith, sum, min)
import qualified Prelude as P

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

-- | Collection of constraints for a monad `m` to support Pull/Push vectors.
type Vectors m = (
  -- expressions needed to implement most Pull/Push vectors operations:
    Value   (Expr m)
  , Cond    (Expr m)
  , Ordered (Expr m)
  , Loop    (Expr m)
  -- constraints needed to support indexing:
  , SyntaxM' m (Expr m Length)
  , Primitive (Expr m) Length
  )

--------------------------------------------------------------------------------
-- ** Manifest vectors.
--------------------------------------------------------------------------------

-- | A 1-dimensional vector with a concrete representation in memory
newtype Manifest m a = M { manifest :: IArray m a }

listManifest :: forall m a .
  ( MonadComp m
  , SyntaxM m a
  , Value (Expr m)
  --
  , Manifestable m (Push m a) a
  --
  , SyntaxM' m (Expr m Length)
  , Primitive (Expr m) Length
  , Num (Internal (Expr m Length))
  , Enum (Internal (Expr m Length))
  )
  => [a]
  -> m (Manifest m a)
listManifest as = manifestFresh (listPush as :: Push m a)

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

instance ( Expr m ~ e
         -- hmm...
         , Cond (Expr m)
         , Ordered (Expr m)
         , SyntaxM' m (Expr m Length)
         , Primitive (Expr m) Length
         , Num (Expr m Length)
         )
    => Slicable e (Pull m a)
  where
    slice from n = take n . drop from

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

-- | Take the head of a vector.
head :: Num (Expr m Index) => Pull m a -> a
head = (!0)

-- | Drop the head of a vector.
tail :: Num (Expr m Length) => Pull m a -> Pull m a
tail = drop 1

-- | Take the 'l' first elements of a vector.
take :: ( Cond (Expr m)
        , Ordered (Expr m)
        , SyntaxM' m (Expr m Length)
        , Primitive (Expr m) Length)
  => Expr m Length -> Pull m a -> Pull m a
take l vec = Pull (min (length vec) l) (vec!)

-- | Drop the 'l' first elements of a vector.
drop :: Num (Expr m Length) => Expr m Length -> Pull m a -> Pull m a
drop l vec = Pull (length vec - l) ((vec!) . (+l))

tails :: Num (Expr m Length) => Pull m a -> Pull m (Pull m a)
tails vec = Pull (length vec + 1) (`drop` vec)

inits :: ( Cond (Expr m)
         , Ordered (Expr m)
         , Num (Expr m Length)
         , SyntaxM' m (Expr m Length)
         , Primitive (Expr m) Length)
  => Pull m a -> Pull m (Pull m a)
inits vec = Pull (length vec + 1) (`take` vec)

replicate :: Expr m Length -> a -> Pull m a
replicate l = Pull l . const

map :: (a -> b) -> Pull m a -> Pull m b
map f vec = Pull (length vec) (f . (vec!))

zip :: ( Cond (Expr m)
       , Ordered (Expr m)
       , SyntaxM' m (Expr m Length)
       , Primitive (Expr m) Length)
  => Pull m a -> Pull m b -> Pull m (a, b)
zip a b = Pull (length a `min` length b) (\i -> (a!i, b!i))

-- | Back-permute a 'Pull' vector using an index mapping. The supplied mapping
--   must be a bijection when restricted to the domain of the vector. This
--   property is not checked, so use with care.
backPermute ::
     (Expr m Length -> Expr m Index -> Expr m Index)
  -> (Pull m a -> Pull m a)
backPermute perm vec = Pull len ((vec!) . perm len)
  where
    len = length vec

reverse :: Num (Expr m Index) => Pull m a -> Pull m a
reverse = backPermute $ \len i -> len-i-1

(...) :: Num (Expr m Index)
    => Expr m Index
    -> Expr m Index
    -> Pull m (Expr m Index)
l ... h = Pull (h-l+1) (+l)

infix 3 ...

zipWith :: ( Cond (Expr m)
           , Ordered (Expr m)
           , SyntaxM' m (Expr m Length)
           , Primitive (Expr m) Length)
  => (a -> b -> c) -> Pull m a -> Pull m b -> Pull m c
zipWith f a b = fmap (uncurry f) $ zip a b

fold :: (Loop (Expr m), SyntaxM m a) => (a -> a -> a) -> a -> Pull m a -> a
fold f init vec = loop (length vec) init $ \i st -> f (vec!i) st

--------------------------------------------------------------------------------

sum :: (Loop (Expr m), Num a, SyntaxM m a) => Pull m a -> a
sum = fold (+) 0

scProd :: ( Loop (Expr m)
          , Cond (Expr m)
          , Ordered (Expr m)
          , Num a
          , SyntaxM m a
          , SyntaxM' m (Expr m Length)
          , Primitive (Expr m) Length)
  => Pull m a -> Pull m a -> a
scProd a b = sum (zipWith (*) a b)

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
class Pushy m vec a | vec -> a, vec -> m
  where
    -- | Convert a vector to 'Push'
    toPush :: vec -> Push m a

instance ( MonadComp m
         -- todo: make an instance instead
         , Indexed (Expr m) (Manifest m a)
         , Finite  (Expr m) (Manifest m a)
         -- hmm...
         , Integral (Internal (Expr m Length))
         , Num (Expr m Length)
         -- hmm...
         , Elem (Manifest m a) ~ a
         , SyntaxM' m (Expr m Length)
         , Primitive (Expr m) Length
         )
    => Pushy m (Manifest m a) a
  where
    toPush = toPush . toPull

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

-- | Create a 'Push' vector from a list of elements.
listPush :: ( MonadComp m
            , SyntaxM m a
            , Value (Expr m)
            -- todo: these really should be part of some 'Vector' class.
            , SyntaxM' m (Expr m Length)
            , Primitive (Expr m) Length
            , Num (Internal (Expr m Length))
            , Enum (Internal (Expr m Length))
            )
  => [a]
  -> Push m a
listPush as = Push (value $ genericLength as) $ \write ->
  sequence_ [write (value i) a | (i, a) <- P.zip [0..] as]

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
forwardPermute :: Pushy m vec a
  => (Expr m Length -> Expr m Index -> Expr m Index) -> vec -> Push m a
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

class ViewManifest m vec a => Manifestable m vec a | vec -> a
  where
    -- | Write the contents of a vector to memory and get its 'Manifest'
    --   vector back. The supplied array may or may not be used for storage.
    manifestArr :: (MonadComp m, SyntaxM m a)
        => Array m a  -- ^ Where to store the vector.
        -> vec        -- ^ Vector to store.
        -> m (Manifest m a)

    default manifestArr
        :: ( MonadComp m
           , SyntaxM m a
           , Pushy m vec a
           , Finite   (Expr m) vec
           , Finite   (Expr m) (Array  m a)
           , Slicable (Expr m) (IArray m a)
           , Num (Expr m Index))
        => Array m a -> vec -> m (Manifest m a)
    manifestArr loc vec = do
        dumpPush v $ \i a -> setArr loc i a
        M <$> unsafeFreezeSlice (length vec) loc
      where
        v = toPush vec

    -- | A version of 'manifest' that allocates a fresh array for the result.
    manifestFresh :: SyntaxM m a => vec -> m (Manifest m a)

    default manifestFresh
        :: ( MonadComp m
           , SyntaxM m a
           , Finite (Expr m) vec)
        => vec
        -> m (Manifest m a)
    manifestFresh vec = do
        loc <- newArr $ length vec
        manifestArr loc vec

    -- | A version of 'manifest' that only stores the vector to the given array.
    manifestStore :: SyntaxM m a => Array m a -> vec -> m ()

    default manifestStore
        :: ( MonadComp m
           , SyntaxM m a
           , Pushy m vec a
           -- hmm...
           , Finite   (Expr m) (Array m a)
           , Slicable (Expr m) (IArray m a)
           , Num (Expr m Length)
           )
        => Array m a
        -> vec
        -> m ()
    manifestStore loc = void . manifestArr loc . toPush

instance ( MonadComp m
         , SyntaxM m a
         , Finite (Expr m) (IArray m a))
    => Manifestable m (Manifest m a) a
  where
    manifestArr _     = return
    manifestFresh     = return
    manifestStore loc = copyArr loc <=< unsafeThawArr . manifest

instance ( MonadComp m
         , SyntaxM   m a
         , Finite   (Expr m) (Array m a)
         , Slicable (Expr m) (IArray m a)
         -- hmm...
         , Integral (Internal (Expr m Length))
         , Num (Expr m Length)
         -- hmm...
         , SyntaxM' m (Expr m Length)
         , Primitive (Expr m) Length
         )
    => Manifestable m (Pull m a) a

instance ( MonadComp m
         , SyntaxM m a
         , Finite   (Expr m) (Array m a)
         , Slicable (Expr m) (IArray m a)
         , Num (Expr m Length)
         )
    => Manifestable m (Push m a) a

--------------------------------------------------------------------------------
