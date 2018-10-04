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

module Data.FirstOrder where

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

data Recovered instr m fs a
  where
    Skip    :: Recovered instr m fs a
    Discard :: instr '(Program m fs, fs) a -> Recovered instr m fs a
    Keep    :: (Variable a, Typeable a)
            => instr '(Program m fs, fs) a -> Recovered instr m fs a

class (HFunctor instr, HTraversable (FirstOrder instr)) =>
    Defunctionalise (instr :: (* -> *, (* -> *, k)) -> * -> *)
  where
    type FirstOrder instr :: (* -> *, (* -> *, k)) -> * -> *
    type FirstOrder instr = instr

    defunctionalise :: MonadFresh m
      => instr '(n, fs) a
      -> m (FirstOrder instr '(n, fs) a)

    default defunctionalise :: (FirstOrder instr ~ instr, MonadFresh m)
      => instr '(n, fs) a
      -> m (FirstOrder instr '(n, fs) a)
    defunctionalise = return

    refunctionalise ::
         ( Defunctionalise n
         , Substitute exp
         )
      => Subst
      -> FirstOrder instr '(Sequence (FirstOrder n) '(exp, fs), '(exp, fs)) a
      -> Recovered instr n '(exp, fs) a

-- refuncInstr ::
--   ( Defunctionalise inv prog
--   , TypeablePred pred
--   , Substitute exp
--   , SubstPred exp ~ pred
--   , pred Bool)
--   => inv -> Subst
--   -> FirstOrder inv instr
--        '(Prog (FirstOrder inv prog) (Param2 exp pred), Param2 exp pred)
--        a
--   -> Refunc instr prog exp pred a

instance (Defunctionalise instr1, Defunctionalise instr2) =>
    Defunctionalise (instr1 :+: instr2)
  where
    type FirstOrder (instr1 :+: instr2) = FirstOrder instr1 :+: FirstOrder instr2

    defunctionalise (Inl x) = fmap Inl (defunctionalise x)
    defunctionalise (Inr x) = fmap Inr (defunctionalise x)
    
    refunctionalise s (Inl x) = case refunctionalise s x of
      Skip      -> Skip      
      Discard i -> Discard (Inl i)
      Keep i    -> Keep (Inl i)
    refunctionalise s (Inr x) = case refunctionalise s x of
      Skip      -> Skip
      Discard i -> Discard (Inr i)
      Keep i    -> Keep (Inr i)

--------------------------------------------------------------------------------

defuncM :: (Defunctionalise instr, DryInterp instr, MonadFresh m)
  => Program instr fs a
  -> m (Sequence (FirstOrder instr) fs a)
defuncM prog = case view prog of
  Return val   -> return (Val val)
  (:>>=) val f -> do
    bind <- dryInterp val
    ins  <- defunctionalise val >>= htraverse defuncM
    tail <- defuncM (f bind)
    return (Seq bind ins tail)

defunc :: (Defunctionalise instr, DryInterp instr)
  => Program instr fs a
  -> Sequence (FirstOrder instr) fs a
defunc prog = evalState (defuncM prog) (0 :: Integer)

--------------------------------------------------------------------------------

refuncM :: (Defunctionalise instr, DryInterp instr, Substitute exp)
  => Subst
  -> Sequence (FirstOrder instr) '(exp, fs) a
  -> Program instr '(exp, fs) a
refuncM _ (Val val) = return val
refuncM s (Seq name instr tail) = case refunctionalise s instr of
  Skip -> refuncM s tail
  Discard instr -> do
    singleton instr
    refuncM s tail
  Keep instr -> do
    new <- singleton instr
    refuncM (extendSubst name new s) tail

refunc :: (Defunctionalise instr, DryInterp instr, Substitute exp)
  => Sequence (FirstOrder instr) '(exp, fs) a
  -> Program instr '(exp, fs) a
refunc = refuncM Map.empty

--------------------------------------------------------------------------------
