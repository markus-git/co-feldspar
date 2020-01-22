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

import Prelude hiding (take, drop, reverse, length, zip, zipWith, sum, min, div, (<), (>=))
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

-- | Collection of constraints for `exp` to support Pull/Push vectors.
type Vector exp = (
  -- expressions needed to implement most Pull/Push vectors operations:
    Value     exp
  , Cond      exp
  , Ordered   exp
  , Iterate   exp
  -- constraints needed to support indexing:
  , Primitive exp Length
  , Syntax'   exp (exp Length)
  , Num           (exp Length)
  )

-- | ...
type VectorM m = Vector (Expr m)

--------------------------------------------------------------------------------
-- ** Manifest vectors.
--------------------------------------------------------------------------------

-- | A 1-dimensional vector with a concrete representation in memory
newtype Manifest m a = M { manifest :: IArray m a }

instance Finite exp (IArray m a) => Finite exp (Manifest m a)
  where
    length (M arr) = length arr

instance Indexed exp (IArray m a) => Indexed exp (Manifest m a)
  where
    type ArrElem (Manifest m a) = ArrElem (IArray m a)
    (!) (M arr) ix = arr ! ix

instance Slicable exp (IArray m a) => Slicable exp (Manifest m a)
  where
    slice ix len (M arr) = M $ slice ix len arr

listManifest :: forall m a .
  ( MonadComp m
  , SyntaxM   m a
  , VectorM   m
  , Loop      m
  -- ToDo: These two constraints are quite common.
  , Finite   (Expr m) (Array  m a)
  , Slicable (Expr m) (IArray m a)
  -- ToDo: Inherited from `listPush`.
  , Num  (Internal (Expr m Length))
  , Enum (Internal (Expr m Length))
  )
  => [a]
  -> m (Manifest m a)
listManifest as = manifestFresh (listPush as :: Push m a)

--------------------------------------------------------------------------------
-- * Pull vectors.
--------------------------------------------------------------------------------

-- | 1-dimensional pull vector: a vector representation that supports random
--   access and fusion of operations.
data Pull (exp :: * -> *) (a :: *) where
    Pull :: exp Length       -- ^ Length of vector.
         -> (exp Index -> a) -- ^ Index function.
         -> Pull exp a

instance Functor (Pull exp)
  where
    fmap f (Pull len ixf) = Pull len (f . ixf)

instance Finite exp (Pull exp a)
  where
    length (Pull len _) = len

instance Indexed exp (Pull exp a)
  where
    type ArrElem (Pull exp a) = a
    (Pull _ ixf) ! i = ixf i

instance (Vector exp, ExprOf a ~ exp) => Slicable exp (Pull exp a)
  where
    slice from n = take n . drop from

type instance ExprOf (Pull exp a) = exp

-- | Data structures that are 'Pull'-like.
class    ( Indexed exp vec
         , Finite  exp vec
         , a   ~ ArrElem vec
         , exp ~ ExprOf a)
        => Pully exp vec a

instance ( Indexed exp vec
         , Finite  exp vec
         , a   ~ ArrElem vec
         , exp ~ ExprOf a)
        => Pully exp vec a

--------------------------------------------------------------------------------
-- ** Pully operations.
--------------------------------------------------------------------------------

-- | Convert a 'Pully' vector to 'Pull' vector.
toPull :: Pully exp vec a => vec -> Pull exp a
toPull vec = Pull (length vec) (vec!)

-- | Take the head of a vector.
head :: forall exp vec a . (Vector exp, Pully exp vec a) => vec -> a
head = (!(0 :: exp Index))

-- | Take the 'l' first elements of a vector.
take :: (Vector exp, Pully exp vec a) => exp Length -> vec -> Pull exp a
take l vec = Pull (min (length vec) l) (vec!)

-- | Drop the 'l' first elements of a vector.
drop :: (Vector exp, Pully exp vec a) => exp Length -> vec -> Pull exp a
drop l vec = Pull (length vec - l) ((vec!) . (+l))

-- | Drop the head of a vector.
tail :: (Vector exp, Pully exp vec a) => vec -> Pull exp a
tail = drop 1

-- | Returns all final segments of the argument, longest first.
tails :: (Vector exp, Pully exp vec a) => vec -> Pull exp (Pull exp a)
tails vec = Pull (length vec + 1) (`drop` vec)

-- | Returns all initial segments of the argument, longest first.
inits :: (Vector exp, Pully exp vec a) => vec -> Pull exp (Pull exp a)
inits vec = Pull (length vec + 1) (`take` vec)

-- | `replicate l x` returns a vector of length `l` with `x` the value of every
--   element
replicate :: exp Length -> a -> Pull exp a
replicate l = Pull l . const

-- | `map f xs` is the vector obtained by applying `f` to each element of `xs`.
map :: Pully exp vec a => (a -> b) -> vec -> Pull exp b
map f vec = Pull (length vec) (f . (vec!))

-- | Zips togheter two vectors and returns vector of corresponding pairs.
zip :: (Vector exp, Pully exp vec1 a, Pully exp vec2 b)
  => vec1 -> vec2 -> Pull exp (a, b)
zip a b = Pull (length a `min` length b) (\i -> (a!i, b!i))

-- | Back-permute a `Pully` vector using an index mapping. The supplied mapping
--   must be a bijection when restricted to the domain of the vector. This
--   property is not checked, so use with care.
backPermute :: Pully exp vec a
  => (exp Length -> exp Index -> exp Index)
  -> (vec -> Pull exp a)
backPermute perm vec = Pull len ((vec!) . perm len)
  where
    len = length vec

-- | Reverses a vector.
reverse :: (Vector exp, Pully exp vec a) => vec -> Pull exp a
reverse = backPermute $ \len i -> len-i-1

-- | Returns a vector over the indices in the given range.
(...) :: Num (exp Index) => exp Index -> exp Index -> Pull exp (exp Index)
l ... h = Pull (h-l+1) (+l)

infix 3 ...

-- | Generalised version of `zip` that combines elements using the supplied
--   function, rather than tupeling.
zipWith :: (Vector exp, Pully exp vec1 a, Pully exp vec2 b)
  => (a -> b -> c) -> vec1 -> vec2 -> Pull exp c
zipWith f a b = fmap (uncurry f) $ zip a b

-- | Fold the elements in the vector using the given rigth-associativ binary
--   operator.
fold :: (Syntax exp a, Vector exp, Pully exp vec a)
  => (a -> a -> a) -> a -> vec -> a
fold f init vec = iter (length vec) init $ \i st -> f (vec!i) st

-- | Sums the elements in a vector.
sum :: (Syntax exp a, Num a, Vector exp, Pully exp vec a) => vec -> a
sum = fold (+) 0

-- | Scalar product of two vectors.
scProd :: (Syntax exp a, Num a, Vector exp, Pully exp vec a) => vec -> vec -> a
scProd a b = sum (zipWith (*) a b)

--------------------------------------------------------------------------------
-- * Push vectors.
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


instance (Expr m ~ exp) => Finite exp (Push m a)
  where
    length (Push len _) = len

-- | Vectors that can be converted to 'Push' vectors.
class Pushy m vec a | vec -> a
  where
    -- | Convert a vector to a 'Push' vector.
    toPush :: vec -> Push m a

-- | A version of 'toPush' that constrains the @m@ argument of 'Push' to that of
--   the monad in which the result is returned. This can be a convenient way to
--   avoid unresolved overloading.
toPushM :: (Pushy m vec a, Monad m) => vec -> m (Push m a)
toPushM = return . toPush

instance (MonadComp m, VectorM m, Loop m, Pully (Expr m) (IArray m a) a)
    => Pushy m (Manifest m a) a
  where
    toPush = toPush . toPull

-- ToDo: `exp ~ ...` hmm...
instance (MonadComp m, VectorM m, Loop m, exp ~ Expr m)
    => Pushy m (Pull exp a) a
  where
    toPush vec = Push len $ \write ->
      for 0 1 (len - 1) $ \i ->
        write i (vec ! i)
      where
        len = length vec

instance (m1 ~ m2) => Pushy m1 (Push m2 a) a
  where
    toPush = id

instance (MonadComp m1, Loop m1, VectorM m1, m1 ~ m2) => Pushy m1 (Seq m2 a) a
  where
    toPush (Seq len init) = Push len $ \write ->
      do next <- init
         for 0 1 (len - 1) $ \i -> do
           a <- next i
           write i a

--------------------------------------------------------------------------------
-- ** Push operations.
--------------------------------------------------------------------------------

-- | Dump the contents of a 'Push' vector.
dumpPush
  :: Push m a                     -- ^ Vector to dump.
  -> (Expr m Index -> a -> m ())  -- ^ Function that writes one element.
  -> m ()
dumpPush (Push _ dump) = dump

-- | Create a 'Push' vector from a list of elements.
listPush ::
  ( Monad m
  , VectorM m
  -- ^ ToDo: Are these necessary? Used to generate indices for each element.
  , Num  (Internal (Expr m Length))
  , Enum (Internal (Expr m Length))
  )
  => [a]
  -> Push m a
listPush as = Push (value $ genericLength as) $ \write ->
  sequence_ [write (value i) a | (i, a) <- P.zip [0..] as]

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
concat :: (Pushy m vec1 vec2, Pushy m vec2 a, Num (Expr m Length), Monad m)
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

-- | Embed the effects in the elements into the internal effects of a 'Push'
-- vector
--
-- __WARNING:__ This function should be used with care, since it allows hiding
-- effects inside a vector. These effects may be (seemingly) randomly
-- interleaved with other effects when the vector is used.
--
-- The name 'sequens' has to do with the similarity to the standard function
-- 'sequence'.
sequens :: (Pushy m vec (m a), Monad m) => vec -> Push m a
sequens vec = Push (length v) $ \write ->
    dumpPush v $ \i m ->
      m >>= write i
  where
    v = toPush vec

-- | Forward-permute a 'Push' vector using an index mapping. The supplied
--   mapping must be a bijection when restricted to the domain of the vector.
--   This property is not checked, so use with care.
forwardPermute :: (Pushy m vec a)
  => (Expr m Length -> Expr m Index -> Expr m Index) -> vec -> Push m a
forwardPermute p vec = Push len $ \write ->
    dumpPush v $ \i a ->
      write (p len i) a
  where
    v   = toPush vec
    len = length v

pairwise :: (SyntaxM m a, SyntaxM m (Expr m Length), PredOf (Expr m) (Internal (Expr m Length)), Loop m, Num (Expr m Length), PredOf (Expr m) Length, Multiplicative (Expr m), References m, Ordered (Expr m), Control m, Pully (Expr m) vec a) =>
  (Expr m Index -> (Expr m Index, Expr m Index)) ->
  vec -> Push m a
pairwise idxs vec =
  Push (length vec) $ \write -> do
    for 1 1 (length vec) $ \i -> do
      let (idx1, idx2) = idxs (i-1)
      iff (idx1 >= idx2) (return ()) $ do
        x <- shareM (vec ! idx1)
        y <- shareM (vec ! idx2)
        write idx1 x
        write idx2 y

-- | Convert a vector to a push vector that computes @n@ elements in each step.
-- This can be used to achieve loop unrolling.
--
-- The length of the vector must be divisible by the number of unrolling steps.
unroll
  :: ( Pully (Expr m) vec a
     , Monad m, Assert m
     , SyntaxM' m (Expr m Word32)
     , Internal (ExprOf a Word32) ~ Word32
     , Loop m     
     , References m
     , Value (Expr m)
     , Multiplicative (Expr m)
     , Equality (Expr m)
     , Num (Expr m Word32)
     )
    => Length  -- ^ Number of steps to unroll
    -> vec
    -> Push m a
unroll 0 _   = Prelude.error "unroll: cannot unroll 0 steps"
unroll 1 vec = Push len $ \write -> do
    for 0 1 (len-1) $ \i -> write i (vec!i)
  where
    len = length vec
unroll n vec = Push len $ \write -> do
    assert
      ((len `Feldspar.mod` value n) Feldspar.== 0)
      ("unroll: length not divisible by " Prelude.++ show n)
    for 0 n' (len-1) $ \i -> Prelude.sequence_
        [ do k <- shareM (i + value j)
             write k (vec!k)
        | j <- [0..n-1]]
  where
    n'  = Prelude.fromIntegral n
    len = length vec

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

data Seq m a
  where
    Seq :: Expr m Length -> m (Expr m Index -> m a) -> Seq m a

instance Monad m => Functor (Seq m)
  where
    fmap f (Seq len init) = Seq len $
      do next <- init
         return $ fmap f . next

instance (Expr m ~ exp) => Finite exp (Seq m a)
  where
    length (Seq len _) = len

class Sequence m vec a | vec -> a
  where
    toSeq :: vec -> Seq m a

toSeqM :: (Sequence m vec a, Monad m) => vec -> m (Seq m a)
toSeqM = return . toSeq

instance (m1 ~ m2) => Sequence m1 (Seq m2 a) a
  where
    toSeq = id

instance
       ( SyntaxM m a
       , ArrElem (IArray m a) ~ a
       , Indexed (Expr m) (IArray m a)
       , Finite  (Expr m) (IArray m a)
       , MonadComp m
       )
    => Sequence m (Manifest m a) a
  where
    toSeq = toSeq . toPull

instance
       ( Expr m ~ exp
       , ArrElem (IArray m a) ~ a
       , Indexed (Expr m) (IArray m a)
       , Finite  (Expr m) (IArray m a)
       , MonadComp m
       )
    => Sequence m (Pull exp a) a
  where
    toSeq vec = Seq (length vec) $ return $ \i -> return $ vec ! i

--------------------------------------------------------------------------------

recurrenceI
  :: ( Pushy     m fvec a
     , Sequence  m ivec a
     , MonadComp m
     )
  => fvec
  -> ivec
  -> (Pull m a -> b)
  -> Seq m b
recurrenceI ibuf ivec step = Seq len $
  do next <- init
     buf  <- undefined
     undefined
  where
    Seq len init = toSeq ivec
-- ...

--------------------------------------------------------------------------------
-- * Writing to memory.
--------------------------------------------------------------------------------

class ViewManifest m vec a | vec -> a
  where
    -- | Try to cast a vector to 'Manifest' directly.
    viewManifest :: vec -> Maybe (Manifest m a)
    viewManifest _ = Nothing

instance ViewManifest m (Pull exp a) a
instance ViewManifest m (Push m a) a
instance ViewManifest m (Seq m a) a
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
           , SyntaxM   m a
           , Pushy     m vec a
           , Finite   (Expr m) vec
           , Finite   (Expr m) (Array  m a)
           , Slicable (Expr m) (IArray m a)
           , Num (Expr m Index)
           )
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
           , SyntaxM   m a
           , Finite (Expr m) vec
           )
        => vec
        -> m (Manifest m a)
    manifestFresh vec = do
        loc <- newArr $ length vec
        manifestArr loc vec

    -- | A version of 'manifest' that only stores the vector to the given array.
    manifestStore :: SyntaxM m a => Array m a -> vec -> m ()

    default manifestStore
        :: ( MonadComp m
           , SyntaxM   m a
           , VectorM   m
           , Loop      m
           , Finite   (Expr m) (Array  m a)
           , Slicable (Expr m) (IArray m a)
           , Num (Expr m Length)
           -- todo: Why isn't this free?
           , Pushy m vec a
           )
        => Array m a
        -> vec
        -> m ()
    manifestStore loc v = void $ manifestArr loc (toPush v :: Push m a)

instance (MonadComp m, SyntaxM m a, Loop m, Finite (Expr m) (IArray m a))
    => Manifestable m (Manifest m a) a
  where
    manifestArr _     = return
    manifestFresh     = return
    manifestStore loc = copyArr loc <=< unsafeThawArr . manifest

  -- ToDo: `exp ~ ...` hmm...
instance (
    MonadComp m
  , SyntaxM   m a
  , VectorM   m
  , Loop      m
  , Finite   exp (Array m a)
  , Slicable exp (IArray m a)
  , exp ~ Expr m
  )
  => Manifestable m (Pull exp a) a

instance (
    MonadComp m
  , SyntaxM   m a
  , VectorM   m
  , Loop      m
  , Finite   (Expr m) (Array m a)
  , Slicable (Expr m) (IArray m a)
  )
  => Manifestable m (Push m a) a

instance (
    MonadComp m
  , SyntaxM   m a
  , VectorM   m
  , Loop      m
  , Finite   (Expr m) (Array m a)
  , Slicable (Expr m) (IArray m a)
  )
  => Manifestable m (Seq m a) a

--------------------------------------------------------------------------------
