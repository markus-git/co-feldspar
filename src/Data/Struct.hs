{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language Rank2Types #-}

module Data.Struct where

--------------------------------------------------------------------------------
-- * Representation.
--------------------------------------------------------------------------------

-- | Typed binary tree structure
data Struct pred con a
  where
    Node   :: pred a => con a -> Struct pred con a
    Branch :: Struct pred con a -> Struct pred con b -> Struct pred con (a, b)

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

-- | Monadic map over a `Struct`
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

--------------------------------------------------------------------------------
