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
{-# language FunctionalDependencies #-}

module Control.Monad.FirstOrder where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Operational.Higher

import Data.Constraint
import Data.Typeable
import Data.Maybe (fromMaybe)

import qualified Data.Map.Strict as Map

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

class DryInterp instr
  where
    dryInterp :: MonadFresh n => instr '(m, fs) a -> n a

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

data Var   = forall a . Typeable a => Var String a
type Subst = Map.Map Var Var

class Substitute exp
  where
    type SubstPred exp :: * -> Constraint
    subst :: SubstPred exp a => Subst -> exp a -> exp a

class Variable a
  where
    ident :: Typeable a => a -> Var -- todo

instance Eq Var
  where
    x == y = compare x y == EQ

instance Ord Var
  where
    compare (Var ix x) (Var iy y) =
      compare (typeOf x) (typeOf y) `mappend` compare ix iy

extendSubst :: (Variable a, Typeable a) => a -> a -> Subst -> Subst
extendSubst x y = Map.insert (ident x) (ident y)

lookupSubst :: (Variable a, Typeable a) => Subst -> a -> a
lookupSubst s x = fromMaybe x $ do
  Var _ y <- Map.lookup (ident x) s
  return $ fromMaybe (error "type error in subst") (cast y)

--------------------------------------------------------------------------------

data Recovered instr jnstr fs a
  where
    Skip    :: Recovered instr jnstr fs a
    Discard :: instr '(Program jnstr fs, fs) a -> Recovered instr jnstr fs a
    Keep    :: (Variable a, Typeable a)
            => instr '(Program jnstr fs, fs) a -> Recovered instr jnstr fs a

class (HFunctor instr, HTraversable (FirstOrder inv instr)) =>
    Defunctionalise inv (instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *)
  where
    type FirstOrder inv instr :: (* -> *, (* -> *, (* -> Constraint, *))) -> * -> *
    type FirstOrder inv instr = instr

    defunctionalise :: MonadFresh m
      => inv
      -> instr '(n, fs) a
      -> m (FirstOrder inv instr '(n, fs) a)

    default defunctionalise :: (FirstOrder inv instr ~ instr, MonadFresh m)
      => inv
      -> instr '(n, fs) a
      -> m (FirstOrder inv instr '(n, fs) a)
    defunctionalise _ = return

    refunctionalise ::
         ( Defunctionalise inv jnstr
         , Substitute exp
         , SubstPred exp ~ pred
         )
      => inv
      -> Subst
      -> FirstOrder inv instr '(Sequence (FirstOrder inv jnstr) (Param2 exp pred), (Param2 exp pred)) a
      -> Recovered instr jnstr (Param2 exp pred) a

instance (Defunctionalise inv instr1, Defunctionalise inv instr2) =>
    Defunctionalise inv (instr1 :+: instr2)
  where
    type FirstOrder inv (instr1 :+: instr2) =
      FirstOrder inv instr1 :+: FirstOrder inv instr2

    defunctionalise inv (Inl x) = fmap Inl (defunctionalise inv x)
    defunctionalise inv (Inr x) = fmap Inr (defunctionalise inv x)
    
    refunctionalise inv s (Inl x) = case refunctionalise inv s x of
      Skip      -> Skip      
      Discard i -> Discard (Inl i)
      Keep i    -> Keep (Inl i)
    refunctionalise inv s (Inr x) = case refunctionalise inv s x of
      Skip      -> Skip
      Discard i -> Discard (Inr i)
      Keep i    -> Keep (Inr i)

--------------------------------------------------------------------------------

defuncM :: (Defunctionalise inv instr, DryInterp instr, MonadFresh m)
  => inv
  -> Program instr fs a
  -> m (Sequence (FirstOrder inv instr) fs a)
defuncM inv prog = case view prog of
  Return val   -> return (Val val)
  (:>>=) val f -> do
    bind <- dryInterp val
    ins  <- defunctionalise inv val >>= htraverse (defuncM inv)
    tail <- defuncM inv (f bind)
    return (Seq bind ins tail)

defunc :: (Defunctionalise inv instr, DryInterp instr)
  => inv
  -> Program instr fs a
  -> Sequence (FirstOrder inv instr) fs a
defunc inv prog = evalState (defuncM inv prog) (0 :: Integer)

--------------------------------------------------------------------------------

refuncM :: (Defunctionalise inv instr, DryInterp instr, Substitute exp, SubstPred exp ~ pred)
  => inv
  -> Subst
  -> Sequence (FirstOrder inv instr) (Param2 exp pred) a
  -> Program instr (Param2 exp pred) a
refuncM _   _ (Val val) = return val
refuncM inv s (Seq name instr tail) = case refunctionalise inv s instr of
  Skip -> refuncM inv s tail
  Discard instr -> do
    singleton instr
    refuncM inv s tail
  Keep instr -> do
    new <- singleton instr
    refuncM inv (extendSubst name new s) tail

refunc :: (Defunctionalise inv instr, DryInterp instr, Substitute exp, SubstPred exp ~ pred)
  => inv
  -> Sequence (FirstOrder inv instr) (Param2 exp pred) a
  -> Program instr (Param2 exp pred) a
refunc inv = refuncM inv Map.empty

--------------------------------------------------------------------------------
