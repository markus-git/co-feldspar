{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

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

-- ...

--------------------------------------------------------------------------------
-- * Commands.
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
