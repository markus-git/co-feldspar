{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language Rank2Types #-}

module Data.Struct where

import Control.Monad.Identity

--------------------------------------------------------------------------------
-- * Representation.
--------------------------------------------------------------------------------

-- | Typed binary tree structure
data Struct pred con a
  where
    Node   :: pred a => con a -> Struct pred con a
    Branch :: Struct pred con a -> Struct pred con b -> Struct pred con (a, b)

extractNode :: pred a => Struct pred con a -> con a
extractNode (Node a) = a

--------------------------------------------------------------------------------

toStruct :: Struct pred con a -> a -> Struct pred Identity a
toStruct rep = go rep . Identity
  where
    go :: Struct pred con a -> Identity a -> Struct pred Identity a
    go (Node _) i = Node i
    go (Branch u v) (Identity (a, b)) = Branch (go u (Identity a)) (go v (Identity b))

listStruct :: forall pred cont b c . (forall y . pred y => cont y -> c) -> Struct pred cont b -> [c]
listStruct f = go
  where
    go :: Struct pred cont a -> [c]
    go (Node a)     = [f a]
    go (Branch u v) = go u ++ go v

liftStruct
  :: (pred a, pred b)
  => (con a -> con b)
  -> Struct pred con a
  -> Struct pred con b
liftStruct f (Node a) = Node (f a)

liftStruct2
  :: (pred a, pred b, pred c)
  => (con a -> con b -> con c)
  -> Struct pred con a
  -> Struct pred con b
  -> Struct pred con c
liftStruct2 f (Node a) (Node b) = Node (f a b)

--------------------------------------------------------------------------------
-- ** Operations

-- | Map over a `Struct`.
mapStruct :: forall pred c1 c2 b
  .  (forall a. pred a => c1 a -> c2 a)
  -> Struct pred c1 b
  -> Struct pred c2 b
mapStruct f = go
  where
    go :: Struct pred c1 a -> Struct pred c2 a
    go (Node a) = Node (f a)
    go (Branch a b) = Branch (go a) (go b)

-- | Monadic map over a `Struct`.
mapStructA :: forall m pred c1 c2 b
  .  Applicative m
  => (forall a. pred a => c1 a -> m (c2 a))
  -> Struct pred c1 b
  -> m (Struct pred c2 b)
mapStructA f = go
  where
    go :: Struct pred c1 a -> m (Struct pred c2 a)
    go (Node a) = Node <$> f a
    go (Branch a b) = Branch <$> go a <*> go b

-- | Zip two 'Struct's to a list.
zipListStruct :: forall pred c1 c2 b r
    . (forall a . pred a => c1 a -> c2 a -> r)
    -> Struct pred c1 b
    -> Struct pred c2 b
    -> [r]
zipListStruct f = go
  where
    go :: Struct pred c1 a -> Struct pred c2 a -> [r]
    go (Node a)     (Node b)     = [f a b]
    go (Branch a b) (Branch c d) = go a c ++ go b d

--------------------------------------------------------------------------------
