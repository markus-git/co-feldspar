{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

{-# language FunctionalDependencies #-}

{-# language TypeOperators #-}

module Feldspar.Frontend where

import Feldspar.Sugar
import Feldspar.Representation

import Data.Bits (Bits, FiniteBits)
import Data.Constraint
import Data.Struct
import Data.Proxy
import Data.Word hiding (Word)
--import Data.Ix

import qualified Data.Bits as Bits

-- syntactci.
import Language.Syntactic as S hiding (Equality)

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

import Prelude hiding (length, Word)

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

-- | Short-hand for a `Syntactic` instance over typed values from `dom`.
type Syntax  dom a = (Syntactic a, dom ~ Domain a, Type (PredicateOf dom) (Internal a), Tuples dom)

-- | Short-hand for a `Syntactic` instance over typed primitive values from `dom`.
type Syntax' dom a = (Syntactic a, PrimType (PredicateOf dom) (Internal a), dom ~ Domain a)

--------------------------------------------------------------------------------

type Boolean a = a ~ Bool
type Word a    = a ~ Word32

--------------------------------------------------------------------------------

-- computational instructions.
type Comp m
  = ( Monad m
    , References m
    , Arrays m
    , IArrays m
    , Control m
      -- todo: add control structures and loops.
    , Value (DomainOf m)
    , Share (DomainOf m)
    )

--------------------------------------------------------------------------------
-- ** General constructs.
--------------------------------------------------------------------------------

class Value dom
  where
    value :: Syntax dom a => Internal a -> a

class Share dom
  where
    share :: (Syntax dom a, Syntax dom b)
      => a        -- ^ Value to share.
      -> (a -> b) -- ^ Body in which to share the value.
      -> b

class Cond dom
  where
    cond
      :: (Syntax dom a, Syntax dom b, Boolean (Internal b))
      => b -- ^ condition.
      -> a -- ^ true branch.
      -> a -- ^ false branch.
      -> a

-- | Condition operator; use as follows:
--
-- @
-- cond1 `?` a $
-- cond2 `?` b $
-- cond3 `?` c $
--         default
-- @
(?) :: (Cond dom, Syntax dom a, Syntax dom b, Boolean (Internal b))
    => b  -- ^ Condition
    -> a  -- ^ True branch
    -> a  -- ^ False branch
    -> a
(?) = cond

infixl 1 ?

--------------------------------------------------------------------------------
-- ** Primitive functions.
--------------------------------------------------------------------------------

class Equality dom
  where
    (==) :: ( Syntax' dom a, Eq      (Internal a)
            , Syntax' dom b, Boolean (Internal b)
            )
         => a -> a -> b

infix 4 ==
  
class Equality dom => Ordered dom
  where
    (<)  :: ( Syntax' dom a, Ord     (Internal a)
            , Syntax' dom b, Boolean (Internal b)
            ) => a -> a -> b
    (<=) :: ( Syntax' dom a, Ord     (Internal a)
            , Syntax' dom b, Boolean (Internal b)
            ) => a -> a -> b
    (>)  :: ( Syntax' dom a, Ord     (Internal a)
            , Syntax' dom b, Boolean (Internal b)
            ) => a -> a -> b
    (>=) :: ( Syntax' dom a, Ord     (Internal a)
            , Syntax' dom b, Boolean (Internal b)
            ) => a -> a -> b

infix 4 <, >, <=, >=
    
class Logical dom
  where
    not  :: (Syntax' dom a, Boolean (Internal a)) => a -> a
    (&&) :: (Syntax' dom a, Boolean (Internal a)) => a -> a -> a

infix 3 &&

class Multiplicative dom
  where
    div :: (Syntax' dom a, Integral (Internal a)) => a -> a -> a
  
class Bitwise dom
  where
    (.&.) :: (Syntax' dom a, Bits (Internal a)) => a -> a -> a
    (.|.) :: (Syntax' dom a, Bits (Internal a)) => a -> a -> a
    xor   :: (Syntax' dom a, Bits (Internal a)) => a -> a -> a
    complement
      :: (Syntax' dom a, Bits (Internal a)) => a -> a
    shiftL
      :: ( Syntax' dom a, Bits (Internal a)
         , Syntax' dom b, Word (Internal b))
      => a -> b -> a
    shiftR
      :: ( Syntax' dom a, Bits (Internal a)
         , Syntax' dom b, Word (Internal b))
      => a -> b -> a
    rotateL
      :: ( Syntax' dom a, Bits (Internal a)
         , Syntax' dom b, Word (Internal b))
      => a -> b -> a
    rotateR
      :: ( Syntax' dom a, Bits (Internal a)
         , Syntax' dom b, Word (Internal b))
      => a -> b -> a

bitSize :: forall a. FiniteBits (Internal a) => a -> Word64
bitSize _ = fromIntegral $ Bits.finiteBitSize (a :: Internal a)
  where a = error "Bits.finiteBitSize evaluated its argument"

infixl 8 `shiftL`, `shiftR`, `rotateL`, `rotateR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

class Casting dom
  where
    i2n :: ( Syntax' dom a, Integral (Internal a)
           , Syntax' dom b, Num      (Internal b)
           )
        => a -> b
  
--------------------------------------------------------------------------------
-- arrays.

class Indexed dom ix a
  where
    type Elem a :: *

    (!) :: Syntax dom (Elem a) => a -> ix -> Elem a

class Slicable ix a
  where
    slice :: ix -> ix -> a -> a

class Finite ix a
  where
    length :: a -> ix
    
--------------------------------------------------------------------------------
-- ** Commands.

type SyntaxM  m a = Syntax  (DomainOf m) a
type SyntaxM' m a = Syntax' (DomainOf m) a

--------------------------------------------------------------------------------

class Monad m => References m
  where
    type Reference m :: * -> *
    initRef :: SyntaxM m a => a -> m (Reference m a)
    newRef  :: SyntaxM m a => m (Reference m a)
    getRef  :: SyntaxM m a => Reference m a -> m a
    setRef  :: SyntaxM m a => Reference m a -> a -> m ()
    unsafeFreezeRef
            :: SyntaxM m a => Reference m a -> m a

shareM :: (SyntaxM m a, References m) => a -> m a
shareM a = initRef a >>= unsafeFreezeRef

--------------------------------------------------------------------------------
-- todo: 'Ix m' could be replaced by 'SyntaxM ix, Array.Ix ix => ix' in 'Arrays'
-- if we got rid of the hardcoded 'Data Index' in array definitions.

class Monad m => Arrays m
  where
    type Array m :: * -> *
    type Ix    m :: *
    newArr  :: SyntaxM  m a => Ix m -> m (Array m a)
    initArr :: SyntaxM' m a => [Internal a] -> m (Array m a)
    getArr  :: SyntaxM  m a => Array m a -> Ix m -> m a
    setArr  :: SyntaxM  m a => Array m a -> Ix m -> a -> m ()
    copyArr :: SyntaxM  m a => Array m a -> Array m a -> m ()

class Arrays m => IArrays m
  where
    type IArray m :: * -> *
    unsafeFreezeArr :: (SyntaxM m a, Finite (Ix m) (Array  m a))
      => Array  m a -> m (IArray m a)
    unsafeThawArr   :: (SyntaxM m a, Finite (Ix m) (IArray m a))
      => IArray m a -> m (Array  m a)

freezeArr :: (IArrays m, SyntaxM m a, Finite (Ix m) (Array m a))
  => Array  m a -> m (IArray m a)
freezeArr arr =
  do iarr <- newArr (length arr)
     copyArr iarr arr
     unsafeFreezeArr iarr

thawArr :: (IArrays m, SyntaxM m a, Finite (Ix m) (IArray m a))
  => IArray m a -> m (Array  m a)
thawArr iarr =
  do brr <- unsafeThawArr iarr -- hahah
     arr <- newArr (length iarr)
     copyArr arr brr
     return arr

--------------------------------------------------------------------------------

class Monad m => Control m
  where
    iff :: (SyntaxM  m a, Boolean  (Internal a))
      => a    -- ^ condition
      -> m () -- ^ true branch
      -> m () -- ^ false branch
      -> m ()
    while :: (SyntaxM  m a, Boolean  (Internal a))
      => m a  -- ^ check
      -> m () -- ^ body
      -> m ()
    for :: (SyntaxM' m a, Integral (Internal a))
      => a    -- ^ lower bound (inclusive)
      -> a    -- ^ upper bound (inclusive)
      -> (a -> m ()) -- ^ step function
      -> m ()

--------------------------------------------------------------------------------
