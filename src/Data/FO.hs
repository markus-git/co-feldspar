{-# language Rank2Types #-}
{-# language TypeOperators #-}
{-# language DataKinds #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language DefaultSignatures #-}
{-# language PolyKinds #-}

{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}

module Data.FO where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Operational.Higher

import Data.Constraint
import Data.Typeable

--------------------------------------------------------------------------------
-- * First-order representation of programs.
--------------------------------------------------------------------------------

-- | First-Order representation of programs, as a sequence of instructions.
data Sequence instr fs a
  where
    Val :: a -> Sequence instr fs a
    Seq :: b                                -- Binder.
        -> instr '(Sequence instr fs, fs) b -- Instruction.
        -> Sequence instr fs a
        -> Sequence instr fs a
  deriving Typeable

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

class Monad m => MonadFresh m
  where
    fresh :: m Integer
    default fresh :: (m ~ t n, MonadTrans t, MonadFresh n) => m Integer
    fresh = lift fresh

instance Monad m => MonadFresh (StateT Integer m)
  where
    fresh = do
      ix <- get
      put (ix + 1)
      return ix

--------------------------------------------------------------------------------

class DryInterp instr
  where
    dryInterp :: MonadFresh n => instr '(m, fs) a -> n a

--------------------------------------------------------------------------------

data Recovered instr prog exp pred a
  where
    Skip    :: Recovered instr prog exp pred a
    Keep    :: instr (Param3 (Program prog (Param2 exp pred)) exp pred) a
            -> Recovered instr prog exp pred a
    Discard :: instr (Param3 (Program prog (Param2 exp pred)) exp pred) a
            -> Recovered instr prog exp pred a

class (HFunctor instr, HTraversable (FirstOrder instr)) =>
    Defunctionalise (instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *)
  where
    type FirstOrder instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *
    type FirstOrder instr = instr

    defunctionalise :: MonadFresh m
      => instr (Param3 prog exp pred) a
      -> m (FirstOrder instr (Param3 prog exp pred) a)

    default defunctionalise :: (FirstOrder instr ~ instr, MonadFresh m)
      => instr (Param3 prog exp pred) a
      -> m (FirstOrder instr (Param3 prog exp pred) a)
    defunctionalise = return

    refunctionalise :: Defunctionalise prog
      => FirstOrder instr (Param3 (Sequence (FirstOrder prog) (Param2 exp pred)) exp pred) a
      -> Recovered instr prog exp pred a

instance (Defunctionalise instr1, Defunctionalise instr2) => Defunctionalise (instr1 :+: instr2)
  where
    type FirstOrder (instr1 :+: instr2) = FirstOrder instr1 :+: FirstOrder instr2

    defunctionalise (Inl x) = fmap Inl (defunctionalise x)
    defunctionalise (Inr x) = fmap Inr (defunctionalise x)
    
    refunctionalise (Inl x) = case refunctionalise x of
      Keep i    -> Keep (Inl i)
      Discard i -> Discard (Inl i)
      Skip      -> Skip
    refunctionalise (Inr x) = case refunctionalise x of
      Keep i    -> Keep (Inr i)
      Discard i -> Discard (Inr i)
      Skip      -> Skip

--------------------------------------------------------------------------------

defuncM :: (Defunctionalise instr, DryInterp instr, MonadFresh m)
  => Program instr (Param2 exp pred) a
  -> m (Sequence (FirstOrder instr) (Param2 exp pred) a)
defuncM prog = case view prog of
  Return val   -> return (Val val)
  (:>>=) val f -> do
    bind <- dryInterp val
    ins  <- defunctionalise val >>= htraverse defuncM
    tail <- defuncM (f bind)
    return (Seq bind ins tail)

refuncM :: ()
refuncM = undefined

--------------------------------------------------------------------------------

defunc :: (Defunctionalise instr, DryInterp instr)
  => Program  (instr)            (Param2 exp pred) a
  -> Sequence (FirstOrder instr) (Param2 exp pred) a
defunc prog = evalState (defuncM prog) (0 :: Integer)

refunc :: (Defunctionalise instr, DryInterp instr)
  => Sequence (FirstOrder instr) (Param2 exp pred) a
  -> Program  (instr)            (Param2 exp pred) a
refunc = undefined

--------------------------------------------------------------------------------
