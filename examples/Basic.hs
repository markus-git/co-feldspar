module Basic where

import Feldspar.Software

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

basic :: Software ()
basic = do
  let zero = 0 :: Data Int8
      one  = 1 :: Data Int8
      
  a <- initRef zero
  u <- getRef a
  setRef a (u `plus` one)

--------------------------------------------------------------------------------

-- initRef :: (MonadCo m a, Syntax a) => a -> m (Ref a)

-- type MonadCo m a = (MonadComp m, Comp m a)
--
-- type Syntax a = (Syntactic a, Type (Constructor a) (Internal a))
  
-- class
--  ( Expr m ~ Constructor a
--  , Pred m ~ PredOf (Constructor a)
--  , PrimDict    (Expr m)
--  , Imp.FreeExp (Expr m)
--  , Syntactic   (Struct (Pred m) (Expr m) (Internal a))
--  , Constructor (Struct (Pred m) (Expr m) (Internal a)) ~ Expr m
--  , Internal    (Struct (Pred m) (Expr m) (Internal a)) ~ Internal a
--  ) => Comp m a
--
-- instance MonadComp Software
--  where
--    type Expr Software = Data
--    type Pred Software = SoftwarePrimType
--
-- instance Syntactic (Data a)
--  where
--    type Constructor (Data a) = ASTFull SoftwareDomain
--    type Internal    (Data a) = a

--
