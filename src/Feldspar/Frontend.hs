{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

{-# language FunctionalDependencies #-}

module Feldspar.Frontend where

import Feldspar.Representation

import Data.Constraint
import Data.Struct
import Data.Proxy

import Language.Syntactic as S

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

class VAL pred dom | dom -> pred
  where
    value :: (pred (Internal a), dom ~ Domain a, Syntactic a) => Internal a -> a

--------------------------------------------------------------------------------

class NUM pred expr | expr -> pred
  where
    plus :: (pred (Internal (expr a)), Num a) => expr a -> expr a -> expr a

--------------------------------------------------------------------------------

-- | Short-hand for computational monads that support standard expressions.
type CoMonad m   = (MonadComp m, NUM (Pred m) (Expr m))

type CoType  m a = (Syntax' m a, VAL (Pred m) (Domain a))

--------------------------------------------------------------------------------
-- * Commands.
--------------------------------------------------------------------------------

initRef :: forall m a . (MonadComp m, Syntax' m a) => a -> m (Ref a)
initRef = liftComp
        . fmap Ref
        . mapStructA (Imp.initRef)
        . cons
  where
    cons :: forall b . Expression (Pred m) (Expr m) b => b -> Struct (Pred m) (Expr m) (Internal b)
    cons = construct -- *** why do I need to lock expr but not pred? or, why do I need to lock at all?

newRef  :: forall m a . (MonadComp m, Syntax' m a) => m (Ref a)
newRef  = liftComp
        . fmap Ref
        . mapStructA (const Imp.newRef)
        $ (typeRep :: TypeRep (Pred m) (TRep m) (Internal a))

getRef  :: forall m a . (MonadComp m, Syntax' m a) => Ref a -> m a
getRef  = liftComp
        . fmap dest
        . mapStructA getty
        . unRef
  where
    dest :: forall b . Expression (Pred m) (Expr m) b => Struct (Pred m) (Expr m) (Internal b) -> b
    dest = destruct -- *** same as initRef.
      
    getty :: forall b . Pred m b => Imp.Ref b -> Prog (Expr m) (Pred m) (Expr m b)
    getty = withType (Proxy :: Proxy (Pred m)) (Proxy :: Proxy (Expr m)) (Proxy :: Proxy b) Imp.getRef    

setRef :: forall m a . (MonadComp m, Syntax' m a) => Ref a -> a -> m ()
setRef ref = liftComp
       . sequence_
       . (\a -> a :: [Prog (Expr m) (Pred m) ()]) -- why is this needed?
       . zipListStruct setty (unRef ref)
       . cons
  where
    cons :: forall b . Expression (Pred m) (Expr m) b => b -> Struct (Pred m) (Expr m) (Internal b)
    cons = construct -- *** same as initRef.
    
    setty :: forall b . Pred m b => Imp.Ref b -> Expr m b -> Prog (Expr m) (Pred m) ()
    setty = withType (Proxy :: Proxy (Pred m)) (Proxy :: Proxy (Expr m)) (Proxy :: Proxy b) Imp.setRef

{-
initRef :: forall m a . (MonadComp m, CoType m a) => a -> m (Ref a)
initRef = liftComp
       . fmap Ref
       . mapStructA (Imp.initRef)
       . construct

newRef :: forall m a . (MonadComp m, CoType m a) => m (Ref a)
newRef = liftComp
       . fmap Ref
       . mapStructA (const Imp.newRef)
       $ typeRep (Proxy :: Proxy (Domain a))

getRef :: forall m a . (MonadComp m, CoType m a) => Ref a -> m a
getRef = liftComp
       . fmap destruct
       . mapStructA getty
       . unRef
  where
    getty :: forall b . Pred m b => Imp.Ref b -> Prog (Expr m) (Pred m) (Expr m b)
    getty = withType (Proxy :: Proxy (Domain a)) (Proxy :: Proxy b) Imp.getRef

setRef :: forall m a . (MonadComp m, CoType m a) => Ref a -> a -> m ()
setRef ref = liftComp
       . sequence_
       . (\a -> a :: [Prog (Expr m) (Pred m) ()]) -- why is this needed?
       . zipListStruct setty (unRef ref)
       . construct
  where
    setty :: forall b . Pred m b => Imp.Ref b -> Expr m b -> Prog (Expr m) (Pred m) ()
    setty = withType (Proxy :: Proxy (Domain a)) (Proxy :: Proxy b) Imp.setRef
-}
--------------------------------------------------------------------------------
