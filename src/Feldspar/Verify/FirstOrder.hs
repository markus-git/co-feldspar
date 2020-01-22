{-# language DataKinds #-}
{-# language GADTs #-}
{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language DefaultSignatures #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}
{-# language RankNTypes #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}

module Feldspar.Verify.FirstOrder where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Operational.Higher

import Data.Constraint
import Data.Maybe (fromMaybe)
import Data.Typeable

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- * First-order representation of programs.
--------------------------------------------------------------------------------

-- | First-Order representation of programs, as a sequence of instructions.
data Sequence instr fs a
  where
    Val :: a -> Sequence instr fs a
    Seq :: b                                -- Binder.
        -> instr '(Sequence instr fs, fs) b -- Value.
        -> Sequence instr fs a
        -> Sequence instr fs a
  deriving Typeable

--------------------------------------------------------------------------------

data HO instr fs a
  where
    Skip    :: HO instr fs ()
    Unnamed :: instr fs a -> HO instr fs a
    Named   :: (Ex a, Typeable a) => instr fs a -> HO instr fs a

class Defunctionalise inv instr
  where
    type FO inv instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *
    type FO inv instr = instr

    defunc :: Fresh m => inv -> instr fs a -> m (FO inv instr fs a)

    default defunc :: (FO inv instr ~ instr, Fresh m) =>
      inv -> instr fs a -> m (FO inv instr fs a)
    defunc _ = return

    refunc :: (Defunctionalise inv jnstr, Sub exp pred, pred Bool) => inv -> Subst ->
      FO inv instr (Param3 (Sequence (FO inv jnstr) (Param2 exp pred)) exp pred) a ->
      HO     instr (Param3 (Program jnstr (Param2 exp pred)) exp pred) a

instance (Defunctionalise inv instr, Defunctionalise inv jnstr) =>
    Defunctionalise inv (instr :+: jnstr)
  where
    type FO inv (instr :+: jnstr) = FO inv instr :+: FO inv jnstr

    defunc inv (Inl instr) = fmap Inl $ defunc inv instr
    defunc inv (Inr jnstr) = fmap Inr $ defunc inv jnstr

    refunc inv sub (Inl instr) = case refunc inv sub instr of
      Named i   -> Named $ Inl i
      Unnamed i -> Unnamed $ Inl i
      Skip      -> Skip

    refunc inv sub (Inr jnstr) = case refunc inv sub jnstr of
      Named j   -> Named $ Inr j
      Unnamed j -> Unnamed $ Inr j
      Skip      -> Skip

--------------------------------------------------------------------------------

defunctionalise ::
  ( HFunctor instr
  , Symbol instr
  , Defunctionalise inv instr
  , HTraversable (FO inv instr)
  ) =>
  inv -> Program instr fs a -> Sequence (FO inv instr) fs a
defunctionalise inv prg = evalState (defunctionaliseM inv prg) (0 :: Integer)

defunctionaliseM ::
  ( Monad m
  , Fresh m
  , HFunctor instr
  , Symbol instr
  , Defunctionalise inv instr
  , HTraversable (FO inv instr)
  ) =>
  inv -> Program instr fs a -> m (Sequence (FO inv instr) fs a)
defunctionaliseM inv prg = case view prg of
  Return val     -> return (Val val)
  (:>>=) instr f -> do
    binder <- dry instr
    instr' <- defunc inv instr
    fonstr <- htraverse (defunctionaliseM inv) instr'
    tail   <- defunctionaliseM inv (f binder)
    return (Seq binder fonstr tail)

--------------------------------------------------------------------------------

refunctionalise :: (Defunctionalise inv instr, Sub exp pred, pred Bool) =>
  inv ->
  Sequence (FO inv instr) (Param2 exp pred) a ->
  Program instr (Param2 exp pred) a
refunctionalise inv = refunctionaliseM inv Map.empty

refunctionaliseM :: (Defunctionalise inv instr, Sub exp pred, pred Bool) =>
  inv ->
  Subst ->
  Sequence (FO inv instr) (Param2 exp pred) a ->
  Program instr (Param2 exp pred) a
refunctionaliseM _   _   (Val val)       = return val
refunctionaliseM inv sub (Seq n fo tail) =
  case refunc inv sub fo of
    Unnamed instr -> do
      singleton instr
      refunctionaliseM inv sub tail
    Named instr -> do
      new <- singleton instr
      refunctionaliseM inv (extendSubst n new sub) tail
    Skip -> do 
      refunctionaliseM inv sub tail

--------------------------------------------------------------------------------

class HFunctor instr => HTraversable instr
  where
    htraverse :: Applicative f
      => (forall b . prog1 b -> f (prog2 b))
      ->    instr '(prog1, fs) a
      -> f (instr '(prog2, fs) a)
    htraverse _ i = pure (hfmap (\_ -> error "traverse compound instruction") i)

instance (HTraversable f, HTraversable g) => HTraversable (f :+: g)
  where
    htraverse f (Inl x) = fmap Inl (htraverse f x)
    htraverse f (Inr x) = fmap Inr (htraverse f x)
      
--------------------------------------------------------------------------------

class Monad m => Fresh m
  where
    fresh :: m Integer

    default fresh :: (m ~ t n, MonadTrans t, Fresh n) => m Integer
    fresh = lift fresh

instance Monad m => Fresh (StateT Integer m)
  where
    fresh = do i <- get; put (i + 1); return i

freshStr :: Fresh m => String -> m String
freshStr base = do i <- fresh; return (base ++ show i)

--------------------------------------------------------------------------------

class Symbol instr
  where
    dry :: Fresh m => instr fs a -> m a

instance (Symbol instr, Symbol jnstr) => Symbol (instr :+: jnstr)
  where
    dry (Inl instr) = dry instr
    dry (Inr jnstr) = dry jnstr

--------------------------------------------------------------------------------

class Name a
  where
    name :: a -> String

data E
  where
    E :: (Typeable a, Name a) => a -> E

instance Eq E
  where
    x == y = compare x y == EQ

instance Ord E
  where
    compare (E a) (E b) = compare (name a) (name b) `mappend`
      compare (typeOf a) (typeOf b)

class Ex a
  where
    hide :: Typeable a => a -> E

--------------------------------------------------------------------------------

type Subst = Map E E

class Substitute exp
  where
    type SubstPred exp :: * -> Constraint
    subst :: SubstPred exp a => Subst -> exp a -> exp a

class TypeablePred pred
  where
    witnessTypeable :: Dict (pred a) -> Dict (Typeable a)

type Sub exp pred = (Substitute exp, SubstPred exp ~ pred, TypeablePred pred)

extendSubst :: (Ex a, Typeable a) => a -> a -> Subst -> Subst
extendSubst x y = Map.insert (hide x) (hide y)

lookupSubst :: (Ex a, Typeable a) => Subst -> a -> a
lookupSubst sub x = fromMaybe x $ case Map.lookup (hide x) sub of
  Just (E y) -> cast y
  Nothing    -> Nothing

--------------------------------------------------------------------------------
