{-# language TypeFamilies          #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleContexts      #-}
{-# language ConstraintKinds       #-}
{-# language ScopedTypeVariables   #-}
{-# language FunctionalDependencies #-}

module Feldspar.Frontend where

import Feldspar.Sugar
import Feldspar.Representation

import Data.Bits (Bits, FiniteBits)
import Data.Constraint
import Data.Int
import Data.Struct
import Data.Proxy
import Data.Word hiding (Word)

import qualified Data.Bits as Bits

-- syntactic.
import Language.Syntactic as S hiding (Equality)

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

import Prelude hiding (length, Word, (<=))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | ...
type Syn (dom :: * -> *) (pred :: * -> Constraint) (exp :: * -> *) (a :: *) =
  ( Syntactic a
  , Domain a ~ dom
  , Type pred (Internal a)
  , Tuples dom
  )

-- | ...
type Syn' dom pred exp a = (Syn dom pred exp a, PrimType pred (Internal a))

-- | ...
type Syntax  exp a = (Syn  (DomainOf exp) (PredOf exp) exp a, ExprOf a ~ exp)

-- | ...
type Syntax' exp a = (Syn' (DomainOf exp) (PredOf exp) exp a, ExprOf a ~ exp)

-- | ...
type Primitive exp a = PredOf exp a

--------------------------------------------------------------------------------

-- | ...
type SyntaxM  m a = Syntax  (Expr m) a

-- | ...
type SyntaxM' m a = Syntax' (Expr m) a

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

class Value exp
  where
    value :: Syntax exp a => Internal a -> a

class Share exp
  where
    share :: (Syntax exp a, Syntax exp b) => a -> (a -> b) -> b

class Iterate exp
  where
    iter :: Syntax exp st => exp Length -> st -> (exp Index -> st -> st) -> st

class Cond exp
  where
    cond :: Syntax exp a => exp Bool -> a -> a -> a

-- | Condition operator; use as follows:
--
-- @
-- cond1 `?` a $
-- cond2 `?` b $
--         default
-- @
(?) :: (Cond exp, Syntax exp a) => exp Bool -> a -> a -> a
(?) = cond

infixl 1 ?

class Equality exp
  where
    (==) :: (Eq a, Primitive exp a) => exp a -> exp a -> exp Bool

infix 4 ==
  
class Equality exp => Ordered exp
  where
    (<)  :: (Ord a, Primitive exp a) => exp a -> exp a -> exp Bool
    (<=) :: (Ord a, Primitive exp a) => exp a -> exp a -> exp Bool
    (>)  :: (Ord a, Primitive exp a) => exp a -> exp a -> exp Bool
    (>=) :: (Ord a, Primitive exp a) => exp a -> exp a -> exp Bool

infix 4 <, >, <=, >=

min :: (Cond exp, Ordered exp, Syntax exp (exp a), Ord a, Primitive exp a)
    => exp a -> exp a -> exp a
min a b = cond (a <= b) a b

class Logical exp
  where
    not  :: exp Bool -> exp Bool
    (&&) :: exp Bool -> exp Bool -> exp Bool
    (||) :: exp Bool -> exp Bool -> exp Bool

infix 3 &&
infix 2 ||

class Multiplicative exp
  where
    mult :: (Integral a, Primitive exp a) => exp a -> exp a -> exp a
    div  :: (Integral a, Primitive exp a) => exp a -> exp a -> exp a
    mod  :: (Integral a, Primitive exp a) => exp a -> exp a -> exp a
  
class Bitwise exp
  where
    complement :: (Bits a, Primitive exp a) => exp a -> exp a
    (.&.) :: (Bits a, Primitive exp a) => exp a -> exp a -> exp a
    (.|.) :: (Bits a, Primitive exp a) => exp a -> exp a -> exp a
    xor   :: (Bits a, Primitive exp a) => exp a -> exp a -> exp a
    sll   :: ( Bits a,     Primitive exp a
             , Integral b, Primitive exp b)
          => exp a -> exp b -> exp a
    srl   :: ( Bits a,     Primitive exp a
             , Integral b, Primitive exp b)
          => exp a -> exp b -> exp a
    rol   :: ( Bits a,     Primitive exp a
             , Integral b, Primitive exp b)
          => exp a -> exp b -> exp a
    ror   :: ( Bits a,     Primitive exp a
             , Integral b, Primitive exp b)
          => exp a -> exp b -> exp a

infixl 8 `sll`, `srl`, `rol`, `ror`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

shiftL  :: (Bitwise exp, Bits a, Primitive exp a, Integral b, Primitive exp b) => exp a -> exp b -> exp a
shiftL = sll

shiftR  :: (Bitwise exp, Bits a, Primitive exp a, Integral b, Primitive exp b) => exp a -> exp b -> exp a
shiftR = srl

rotateL :: (Bitwise exp, Bits a, Primitive exp a, Integral b, Primitive exp b) => exp a -> exp b -> exp a
rotateL = rol

rotateR :: (Bitwise exp, Bits a, Primitive exp a, Integral b, Primitive exp b) => exp a -> exp b -> exp a
rotateR = ror

(.<<.)  :: (Bitwise exp, Bits a, Primitive exp a, Primitive exp Int32) => exp a -> exp Int32 -> exp a
(.<<.) = shiftL

(.>>.)  :: (Bitwise exp, Bits a, Primitive exp a, Primitive exp Int32) => exp a -> exp Int32 -> exp a
(.>>.) = shiftR

infixl 8 `shiftL`, `shiftR`, `rotateL`, `rotateR`, .<<., .>>.

bitSize :: forall exp a. FiniteBits a => exp a -> Word64
bitSize _ = fromIntegral $ Bits.finiteBitSize (a :: a)
  where a = error "Bits.finiteBitSize evaluated its argument"

ones :: (Bitwise exp, Bits a, Num (exp a), Primitive exp a) => exp a
ones = complement 0

class Casting exp
  where
    i2n :: (Integral a, Primitive exp a, Num b, Primitive exp b) => exp a -> exp b
    i2b :: (Integral a, Primitive exp a, Primitive exp Bool) => exp a -> exp Bool
    b2i :: (Integral a, Primitive exp a, Primitive exp Bool) => exp Bool -> exp a

--------------------------------------------------------------------------------
-- * Instructions.
--------------------------------------------------------------------------------

-- | Computational instructions.
type MonadComp m
  = ( Monad m
    , References m
    , Arrays m
    , IArrays m
    , Control m
    )

--------------------------------------------------------------------------------

class Monad m => References m
  where
    type Reference m :: * -> *
    initRef :: SyntaxM m a => a -> m (Reference m a)
    newRef  :: SyntaxM m a => m (Reference m a)
    getRef  :: SyntaxM m a => Reference m a -> m a
    setRef  :: SyntaxM m a => Reference m a -> a -> m ()
    unsafeFreezeRef :: SyntaxM m a => Reference m a -> m a

shareM :: (SyntaxM m a, References m) => a -> m a
shareM a = initRef a >>= unsafeFreezeRef

--------------------------------------------------------------------------------

class Finite exp arr
  where
    length :: arr -> exp Length

class Indexed exp arr
  where
    type ArrElem arr :: *
    (!) :: arr -> exp Index -> ArrElem arr

class Slicable exp arr
  where
    slice :: exp Index -> exp Length -> arr -> arr

--------------------------------------------------------------------------------

class Monad m => Arrays m
  where
    type Array m :: * -> *
    initArr :: SyntaxM' m a => [Internal a] -> m (Array m a)
    newArr  :: SyntaxM  m a => Expr m Length -> m (Array m a)
    getArr  :: SyntaxM  m a => Array m a -> Expr m Index -> m a
    setArr  :: SyntaxM  m a => Array m a -> Expr m Index -> a -> m ()
    copyArr :: SyntaxM  m a => Array m a -> Array m a -> m ()

--------------------------------------------------------------------------------

class Arrays m => IArrays m
  where
    type IArray m :: * -> *
    unsafeFreezeArr :: (SyntaxM m a, Finite (Expr m) (Array  m a))
      => Array  m a -> m (IArray m a)
    unsafeThawArr   :: (SyntaxM m a, Finite (Expr m) (IArray m a))
      => IArray m a -> m (Array  m a)

freezeArr ::
     ( IArrays m
     , SyntaxM m a
     , Finite (Expr m) (Array m a)
     )
  => Array m a -> m (IArray m a)
freezeArr arr =
  do iarr <- newArr (length arr)
     copyArr iarr arr
     unsafeFreezeArr iarr

thawArr ::
     ( IArrays m
     , SyntaxM m a
     , Finite (Expr m) (IArray m a)
     )
  => IArray m a -> m (Array m a)
thawArr iarr =
  do brr <- unsafeThawArr iarr -- haha.
     arr <- newArr (length iarr)
     copyArr arr brr
     return arr

unsafeFreezeSlice
  :: ( IArrays m
     , SyntaxM m a
     , Finite   (Expr m) (Array  m a)
     , Slicable (Expr m) (IArray m a)
     , Num (Expr m Index)
     )
  => Expr m Length -> Array m a -> m (IArray m a)
unsafeFreezeSlice len = fmap (slice 0 len) . unsafeFreezeArr

--------------------------------------------------------------------------------

class Monad m => Control m
  where
    -- | Conditional statement.
    iff ::
         Expr m Bool     -- ^ Condition.
      -> m ()            -- ^ True branch.
      -> m ()            -- ^ False branch.
      -> m ()

class Monad m => Loop m
  where
    -- | While-loop.
    while ::
         m (Expr m Bool) -- ^ Condition.
      -> m ()            -- ^ Loop body.
      -> m ()

    -- | For-loop.
    for :: (Integral a, SyntaxM' m (Expr m a))
      => Expr m a           -- ^ Lower bound (inclusive).
      -> Int                -- ^ Inc./dec. step.
      -> Expr m a           -- ^ Upper bound (inclusive).
      -> (Expr m a -> m ()) -- ^ Step function.
      -> m ()

class Monad m => Assert m
  where
    break  :: m ()
    assert :: Expr m Bool -> String -> m ()

--------------------------------------------------------------------------------
