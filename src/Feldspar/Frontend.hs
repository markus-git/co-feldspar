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

import Data.Constraint
import Data.Struct

import Language.Syntactic

import qualified Control.Monad.Operational.Higher as Oper (Program, Param2)

-- imperative-edsl
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp (Ref)

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ...
class LET exp where
  shareTag :: (CoType a, CoType b) => String -> exp a -> (exp a -> exp b) -> exp b

-- | ...
share :: (LET exp, CoType a, CoType b) => exp a -> (exp a -> exp b) -> exp b
share = shareTag ""

-- | ...
value :: Syntax a => I a -> a
value = error "todo: value"

--------------------------------------------------------------------------------

-- | ..
class NUM exp where
  plus   :: (Type a, Num a) => exp a -> exp a -> exp a
  minus  :: (Type a, Num a) => exp a -> exp a -> exp a
  times  :: (Type a, Num a) => exp a -> exp a -> exp a
  negate :: (Type a, Num a) => exp a -> exp a
  
--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

-- | ... hidden ...
type Prog pred exp = Oper.Program CoCMD (Oper.Param2 exp pred)

-- | ... NUM (Expr m), ...
class Monad m => MonadComp m
  where
    type Expr m :: * -> *
    type Pred m :: * -> Constraint
         
    liftCo :: Prog (Pred m) (Expr m) a -> m a

--------------------------------------------------------------------------------

class    ( Expr m ~ C a
         , Pred m ~ PredOf a
         , Syn (Struct (Pred m) (Expr m) (I a))
         , C (Struct (Pred m) (Expr m) (I a)) ~ Expr m
         , I (Struct (Pred m) (Expr m) (I a)) ~ I a
         )
         => Co m a

instance ( Expr m ~ C a
         , Pred m ~ PredOf a
         , Syn (Struct (Pred m) (Expr m) (I a))
         , C (Struct (Pred m) (Expr m) (I a)) ~ Expr m
         , I (Struct (Pred m) (Expr m) (I a)) ~ I a
         ) => Co m a

type MonadCo m a = (MonadComp m, Co m a)

--------------------------------------------------------------------------------
-- **

-- | ...
initRef :: (MonadCo m a, Syntax a) => a -> m (Ref a)
initRef = initNamedRef "r"

-- | ...
initNamedRef :: forall m a. (MonadCo m a, Syntax a) => String -> a -> m (Ref a)
initNamedRef name val = liftCo . fmap Ref . mapStructA (Imp.initNamedRef name) $ sugar
  where
    sugar :: Struct (Pred m) (Expr m) (I a)
    sugar = resug val
{-
-- | ...
newRef :: (MonadCo m a, Syntax a) => m (Ref a)
newRef = newNamedRef "r"
-}
-- | ...
newNamedRef
  :: forall m a. (MonadCo m a, Syntax a
     -- bad
     , PredOf a ~ PrimitiveType
     )
  => String -> m (Ref a)
newNamedRef name = liftCo . fmap Ref . mapStructA (const $ Imp.newNamedRef name) $ sugar
  where
    sugar :: Struct PrimitiveType PrimitiveTypeRep (I a)
    sugar = typeRep

--------------------------------------------------------------------------------
