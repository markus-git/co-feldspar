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
{-# language ConstraintKinds #-}

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

instance (DryInterp instr, DryInterp jnstr) => DryInterp (instr :+: jnstr)
  where
    dryInterp (Inl i) = dryInterp i
    dryInterp (Inr j) = dryInterp j

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

freshStr :: MonadFresh m => String -> m String
freshStr base = do
  i <- fresh
  return (base ++ show i)

--------------------------------------------------------------------------------

type family Id a :: *

data Hidden
  where
    Hidden :: (Typeable a, Eq (Id a), Ord (Id a), Show (Id a)) => a -> Id a -> Hidden

instance Eq Hidden
  where
    x == y = compare x y == EQ

instance Ord Hidden
  where
    compare (Hidden vx ix) (Hidden vy iy) =
      compare (show ix) (show iy) `mappend` compare (typeOf vx) (typeOf vy)

class Variable a
  where
    hide :: a -> Hidden

type Subst exp = Map.Map Hidden Hidden

class Substitute exp
  where
    type SubstPred exp :: * -> Constraint
    subst :: SubstPred exp a => Subst exp -> exp a -> exp a

extendSubst :: forall exp a . (Variable a, Typeable a) => a -> a -> Subst exp -> Subst exp
extendSubst x y = Map.insert (hide x) (hide y)

lookupSubst :: forall exp a . (Variable a, Typeable a) => Subst exp -> a -> a
lookupSubst s x = fromMaybe x $
  do (Hidden y _) <- Map.lookup (hide x) s
     return $ fromMaybe (error "type error in subst.") (cast y)

--------------------------------------------------------------------------------

data Recovered instr jnstr exp pred a
  where
    Skip ::
      Recovered instr jnstr exp pred a
    Discard ::
      instr '(Program jnstr (Param2 exp pred), (Param2 exp pred)) a ->
      Recovered instr jnstr exp pred a
    Keep ::
      (Variable a, Typeable a) =>
      instr '(Program jnstr (Param2 exp pred), (Param2 exp pred)) a ->
      Recovered instr jnstr exp pred a

class TypeablePred pred where
  witnessTypeable :: Dict (pred a) -> Dict (Typeable a)

--------------------------------------------------------------------------------

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
         , TypeablePred pred
         , pred Bool
         )
      => inv
      -> Subst exp
      -> FirstOrder inv instr
           (Param3 (Sequence (FirstOrder inv jnstr) (Param2 exp pred)) exp pred) a
      -> Recovered instr jnstr exp pred a

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

refuncM ::
     ( Defunctionalise inv instr
     , Substitute exp
     , SubstPred exp ~ pred
     , TypeablePred pred
     , pred Bool
     )
  => inv
  -> Subst exp
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

refunc ::
     ( Defunctionalise inv instr
     , Substitute exp
     , SubstPred exp ~ pred
     , TypeablePred pred
     , pred Bool
     )
  => inv
  -> Sequence (FirstOrder inv instr) (Param2 exp pred) a
  -> Program instr (Param2 exp pred) a
refunc inv = refuncM inv Map.empty

--------------------------------------------------------------------------------
