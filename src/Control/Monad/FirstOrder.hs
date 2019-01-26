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
-- *
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
    fresh = do {ix <- get; put (ix + 1); return ix}

freshStr :: MonadFresh m => String -> m String
freshStr base = (\i -> base ++ show i) <$> fresh

class DryInterp instr
  where
    dryInterp :: MonadFresh m => instr fs a -> m a

instance (DryInterp instr, DryInterp jnstr) => DryInterp (instr :+: jnstr)
  where
    dryInterp (Inl i) = dryInterp i
    dryInterp (Inr j) = dryInterp j

--------------------------------------------------------------------------------

data Value = forall a. (Typeable a, Eq (Name a), Ord (Name a), Show (Name a)) =>
  Value (Name a) a

instance Eq Value
  where
    x == y = compare x y == EQ

instance Ord Value
  where
    compare (Value nx vx) (Value ny vy) = compare (show nx) (show ny) `mappend`
      compare (typeOf vx) (typeOf vy)

type Sub = Map.Map Value Value

class (Typeable a, Eq (Name a), Ord (Name a), Show (Name a)) => Identify a
  where
    type Name a :: *
    name :: a -> Name a

class Substitute exp
  where
    type SubPred exp :: * -> Constraint
    substitute :: SubPred exp a => Sub -> exp a -> exp a

extendSub :: forall exp a. Identify a => a -> a -> Sub -> Sub
extendSub x y = Map.insert (Value (name x) x) (Value (name y) y)

lookupSub :: forall exp a. Identify a => Sub -> a -> a
lookupSub sub x = case Map.lookup (Value (name x) x) sub of
  Just (Value ny vy) -> case cast vy of
    Just val -> val
    Nothing  -> error "type error in substitution."
  Nothing -> error "could not find substitution."

--------------------------------------------------------------------------------

data Dry instr fs a
  where
    Dry :: a -> instr fs a -> Dry instr fs a

dryTranslate ::
  ( MonadFresh m
  , DryInterp instr
  , HFunctor instr
  , HTraversable (FirstOrder inv instr)
  , Defunctionalise inv instr
  )
  => inv
  -> Sub
  -> Program instr fs a
  -> m (Program (Dry (FirstOrder inv instr)) fs a)
dryTranslate inv sub prog = case view prog of
  Return value   -> return $ return value
  (:>>=) instr f ->
    do name   <- dryInterp instr
       jnstr' <- defunctionalise inv instr
       jnstr  <- htraverse (dryTranslate inv sub) jnstr'
       prog   <- dryTranslate inv sub $ f name
       return $ (singleton (Dry name jnstr)) >>= \val ->
         _ -- dryReplace (extendSub name val sub) prog

dryReplace :: Sub -> Program instr fs a -> Program instr fs a
dryReplace = undefined

{-
    defunctionalise :: MonadFresh m
      => inv
      -> instr '(n, fs) a
      -> m (FirstOrder inv instr '(n, fs) a)
-}

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

data Recovered instr jnstr exp pred a
  where
    Discard ::
      instr '(Program jnstr (Param2 exp pred), (Param2 exp pred)) () ->
      Recovered instr jnstr exp pred ()
    Keep ::
      (Identify a, Typeable a) =>
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

instance (Defunctionalise inv instr1, Defunctionalise inv instr2) =>
    Defunctionalise inv (instr1 :+: instr2)
  where
    type FirstOrder inv (instr1 :+: instr2) =
      FirstOrder inv instr1 :+: FirstOrder inv instr2

    defunctionalise inv (Inl x) = fmap Inl (defunctionalise inv x)
    defunctionalise inv (Inr x) = fmap Inr (defunctionalise inv x)

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

