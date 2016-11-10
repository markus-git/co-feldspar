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

import Data.Constraint
import Data.Struct
import Data.Proxy
--import Data.Ix

-- syntactci.
import Language.Syntactic as S hiding (Equality)

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

-- | Short-hand for a `Syntactic` instance over typed values from `dom`.
type Syntax  dom a = (Syntactic a, dom ~ Domain a, Type (PredicateOf dom) (Internal a), Tuples dom)

-- | Short-hand for a `Syntactic` instance over typed primitive values from `dom`.
type Syntax' dom a = (Syntactic a, PrimType (PredicateOf dom) (Internal a), dom ~ Domain a)

--------------------------------------------------------------------------------

type Boolean a = a ~ Bool

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
      => a -- ^ true branch.
      -> a -- ^ false branch.
      -> b -- ^ condition.
      -> a

--------------------------------------------------------------------------------
-- ** Primitive functions.

class Equality dom
  where
    (==) :: (Syntax' dom a, Syntax' dom b, Eq (Internal a), Boolean (Internal b)) => a -> a -> b
  
class Equality dom => Ordered dom
  where
    (<)  :: (Syntax' dom a, Syntax' dom b, Ord (Internal a), Boolean (Internal b)) => a -> a -> b
  
class Logical dom
  where
    not  :: (Syntax' dom a, Boolean (Internal a)) => a -> a
    (&&) :: (Syntax' dom a, Boolean (Internal a)) => a -> a -> a

infix 3 &&
infix 4 ==
infix 4 <

--------------------------------------------------------------------------------
-- arrays.

class Indexed dom ix a
  where
    type Elem a :: *

    (!) :: Syntax dom (Elem a) => a -> ix -> Elem a

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

--------------------------------------------------------------------------------
-- todo: 'Ix m' could be replaced by 'SyntaxM ix, Array.Ix ix => ix' in 'Arrays'
-- if we got rid of the hardcoded 'Data Index' in array definitions.

class Monad m => Arrays m
  where
    type Array m :: * -> *
    type Ix    m :: *
    newArr :: SyntaxM m a => Ix m -> m (Array m a)
    getArr :: SyntaxM m a => Array m a -> Ix m -> m a
    setArr :: SyntaxM m a => Array m a -> Ix m -> a -> m ()

class Arrays m => IArrays m
  where
    type IArray m :: * -> *
    freezeArr :: (SyntaxM m a, Finite (Ix m) (Array  m a)) => Array  m a -> m (IArray m a)
    thawArr   :: (SyntaxM m a, Finite (Ix m) (IArray m a)) => IArray m a -> m (Array  m a)

--------------------------------------------------------------------------------

class Monad m => Control m
  where
    iff   :: (SyntaxM m a,  Boolean  (Internal a)) => a -> m () -> m () -> m ()
    while :: (SyntaxM m a,  Boolean  (Internal a)) => m a -> m () -> m ()
    for   :: (SyntaxM' m a, Integral (Internal a)) => a -> (a -> m ()) -> m ()

--------------------------------------------------------------------------------
