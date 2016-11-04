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

-- | ... shord-hand for typed values in language m ...
type SyntaxM m a = Syntax (DomainOf m) a

--------------------------------------------------------------------------------

-- computational instructions.
type Comp m
  = ( Monad m
    , References m
      -- todo: add control structures and loops.
    , Value (DomainOf m)
    , Share (DomainOf m)
    )

--------------------------------------------------------------------------------
-- ** General constructs.

-- | ... hmm ...
type Boolean a = a ~ Bool

-- | Literals.
class Value dom
  where
    value :: Syntax dom a => Internal a -> a

-- | Forced evaluation.
class Share dom
  where
    share :: (Syntax dom a, Syntax dom b)
      => a        -- ^ Value to share.
      -> (a -> b) -- ^ Body in which to share the value.
      -> b

-- | Conditional statements.
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

-- | Equality.
class Equality dom
  where
    (==) :: (Syntax' dom a, Syntax' dom b, Eq (Internal a), Boolean (Internal b)) => a -> a -> b

infix 4 ==

-- | Ordered.
class Equality dom => Ordered dom
  where
    (<)  :: (Syntax' dom a, Syntax' dom b, Ord (Internal a), Boolean (Internal b)) => a -> a -> b

infix 4 <

-- | Logical stuff.
class Logical dom
  where
    not  :: (Syntax' dom a, Boolean (Internal a)) => a -> a
    (&&) :: (Syntax' dom a, Boolean (Internal a)) => a -> a -> a

infix 3 &&
    
--------------------------------------------------------------------------------
-- ** Commands.

-- | Commands for managing mutable references.
class Monad m => References m
  where
    type Reference m :: * -> *

    initRef :: SyntaxM m a => a -> m (Reference m a)
    newRef  :: SyntaxM m a => m (Reference m a)
    getRef  :: SyntaxM m a => Reference m a -> m a
    setRef  :: SyntaxM m a => Reference m a -> a -> m ()

--------------------------------------------------------------------------------
