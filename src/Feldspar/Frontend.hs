{-# language TypeFamilies #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

module Feldspar.Frontend where

import Feldspar.Primitive
import Feldspar.Representation
import Feldspar.Sugar

import Data.Constraint
import Data.Struct
import Data.Proxy

import Language.Syntactic hiding (Syntactic(..), SyntacticN(..), resugar, E)

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ...
value :: Syntactic a => Internal a -> a
value = error "todo: value"

--------------------------------------------------------------------------------

-- | ..
class NUM exp where
  plus   :: (PredOf exp a, Num a) => exp a -> exp a -> exp a
  minus  :: (PredOf exp a, Num a) => exp a -> exp a -> exp a
  times  :: (PredOf exp a, Num a) => exp a -> exp a -> exp a
  negate :: (PredOf exp a, Num a) => exp a -> exp a

--------------------------------------------------------------------------------

-- | ... short-hand ...
type ExprComp expr = (NUM expr)

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ... should be hidden ...
type Prog pred exp = Oper.Program CoCMD (Oper.Param2 exp pred)

-- | ... NUM (Expr m), ...
class (Monad m, ExprComp (Expr m)) => MonadComp m
  where
    type Expr m :: * -> *
    type Pred m :: * -> Constraint
         
    liftComp :: Prog (Pred m) (Expr m) a -> m a

--------------------------------------------------------------------------------

class
  ( -- tie language, predicate and expression types togheter.
    Expr m ~ Constructor a
  , Pred m ~ PredOf (Constructor a)
    -- defer imperative-edsl constraints to `Pred m`.
  , PrimDict    (Expr m)
  , Imp.FreeExp (Expr m)
    -- make sure expressions can be interpreted as `Struct`
  , Syntactic   (Struct (Pred m) (Expr m) (Internal a))
  , Constructor (Struct (Pred m) (Expr m) (Internal a)) ~ Expr m
  , Internal    (Struct (Pred m) (Expr m) (Internal a)) ~ Internal a
  ) => Comp m a

instance
  (  -- tie language types and expression types togheter.
    Expr m ~ Constructor a
  , Pred m ~ PredOf (Constructor a)
    -- defer imperative-edsl constraints to `Pred m`.
  , PrimDict    (Expr m)
  , Imp.FreeExp (Expr m)
    -- make sure expressions can be interpreted as `Struct`
  , Syntactic   (Struct (Pred m) (Expr m) (Internal a))
  , Constructor (Struct (Pred m) (Expr m) (Internal a)) ~ Expr m
  , Internal    (Struct (Pred m) (Expr m) (Internal a)) ~ Internal a
  ) => Comp m a

--------------------------------------------------------------------------------

-- | ... short-hand for computational monads with co-design constraints ...
type MonadCo m a = (MonadComp m, Comp m a)

--------------------------------------------------------------------------------
-- **

initRef :: (MonadCo m a, Syntax a) => a -> m (Ref a)
initRef = initNamedRef "r"

initNamedRef :: forall m a. (MonadCo m a, Syntax a) => String -> a -> m (Ref a)
initNamedRef name val = liftComp . fmap Ref . mapStructA (Imp.initNamedRef name) $ sugar
  where
    sugar :: Struct (Pred m) (Expr m) (Internal a)
    sugar = resugar val

--------------------------------------------------------------------------------

newRef :: (MonadCo m a, Syntax a) => m (Ref a)
newRef = newNamedRef "r"

newNamedRef :: forall m a. (MonadCo m a, Syntax a) => String -> m (Ref a)
newNamedRef name = liftComp . fmap Ref . mapStructA (const $ Imp.newNamedRef name) $ sugar
  where
    sugar :: Struct (PredOf (Constructor a)) (RepOf (Constructor a)) (Internal a)
    sugar = typeRep (Proxy :: Proxy a)

--------------------------------------------------------------------------------

getRef :: forall m a. (MonadCo m a, Syntax a) => Ref a -> m a
getRef = liftComp . fmap sugar . mapStructA getty . unRef
  where
    getty :: forall b. Pred m b => Imp.Ref b -> Prog (Pred m) (Expr m) (Expr m b)
    getty = withPrim (Proxy :: Proxy (Expr m)) (Proxy :: Proxy b) Imp.getRef

    sugar :: Struct (Pred m) (Expr m) (Internal a) -> a
    sugar = resugar

--------------------------------------------------------------------------------

setRef :: forall m a. (MonadCo m a, Syntax a) => Ref a -> a -> m ()
setRef ref = liftComp
           . (sequence_ :: [Prog (Pred m) (Expr m) ()] -> Prog (Pred m) (Expr m) ())
           . zipListStruct setty (unRef ref)
           . sugar
  where
    setty :: forall b. Pred m b => Imp.Ref b -> Expr m b -> Prog (Pred m) (Expr m) ()
    setty = withPrim (Proxy :: Proxy (Expr m)) (Proxy :: Proxy b) Imp.setRef
    
    sugar :: a -> Struct (Pred m) (Expr m) (Internal a)
    sugar = resugar

--------------------------------------------------------------------------------
