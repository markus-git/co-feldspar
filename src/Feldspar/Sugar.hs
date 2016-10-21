{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}

-- todo : hmm... consequense of using `sup` in `Syntactic` instance for pairs.
{-# language UndecidableInstances #-}

-- todo : get rid off.
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}

module Feldspar.Sugar where

import Data.Constraint (Constraint)
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))
import Data.Struct

import Language.Syntactic.Syntax
import Language.Syntactic.Sugar
import Language.Syntactic.Decoration

import Language.Syntactic.Functional.Tuple

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Representation of supported feldspar types as typed binary trees over
--   primitive types.
type TypeRep pred rep = Struct pred rep

-- | Representation of supported value types and N-ary functions over such
--   types.
data TypeRepF pred rep a
  where
    ValT :: TypeRep pred rep a -> TypeRepF pred rep a
    FunT :: TypeRep pred rep a -> TypeRepF pred rep b -> TypeRepF pred rep (a -> b)

--------------------------------------------------------------------------------

-- | Supported types.
class (Eq a, Show a, Typeable a) => Type pred rep a
  where
    typeRep :: TypeRep pred rep a

-- pairs of valid types are themselves also valid types.
instance
    ( Type pred trep a
    , Type pred trep b
    )
    => Type pred trep (a, b)
  where
    typeRep = Branch typeRep typeRep

--------------------------------------------------------------------------------

-- | Supported domain decorations.
class Decorated decor a
  where
    decorate :: decor a

-- single valid types are simply lifted.
instance Type pred rep a => Decorated (TypeRepF pred rep) a
  where
    decorate = ValT typeRep

--------------------------------------------------------------------------------

sugarSymDecorated
    :: ( Signature sig
       , fi             ~ SmartFun (sup :&: info) sig
       , sig            ~ SmartSig fi
       , (sup :&: info) ~ SmartSym fi
       , Decorated info (DenResult sig)
       , SyntacticN f fi
       , sub :<: sup
       )
    => sub sig -> f
sugarSymDecorated = sugarSymDecor decorate

--------------------------------------------------------------------------------

instance
    ( Syntactic a
    , Syntactic b
    , Domain b       ~ Domain a
    , (sup :&: info) ~ Domain a
    , Tuple :<: sup
      -- hmm...
    , Decorated info (Internal a, Internal b)
    , Decorated info (Internal a)
    , Decorated info (Internal b)
    )
    => Syntactic (a, b)
  where
    type Domain   (a, b) = Domain a
    type Internal (a, b) = (Internal a, Internal b)

    desugar (a, b) = sugarSymDecorated Pair (desugar a) (desugar b)
    sugar ab = (sugarSymDecorated Fst ab, sugarSymDecorated Snd ab)

--------------------------------------------------------------------------------


{-
--------------------------------------------------------------------------------

class Syntactic a
  where
    type Constructor a :: * -> *
    type Internal    a :: *

    desugar :: a -> Constructor a (Internal a)
    sugar   :: Constructor a (Internal a) -> a

-- | Associate a syntactical object with its predicate type.
type family PredOf (a :: * -> *) :: * -> Constraint

-- | Syntactic type casting.
resugar :: (Syntactic a, Syntactic b, Constructor a ~ Constructor b, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar

--------------------------------------------------------------------------------

instance Syntactic (ASTFull sym a)
  where
    type Constructor (ASTFull sym a) = ASTFull sym
    type Internal    (ASTFull sym a) = a

    desugar = id
    sugar   = id

--------------------------------------------------------------------------------

class SyntacticN f internal | f -> internal
  where
    desugarN :: f -> internal
    sugarN   :: internal -> f

instance {-# overlapping #-} (Syntactic f, fi ~ Constructor f (Internal f))
    => SyntacticN f fi
  where
    desugarN = desugar
    sugarN   = sugar

instance {-# overlapping #-} (Syntactic a, c ~ Constructor a, i ~ Internal a, SyntacticN f fi)
    => SyntacticN (a -> f) (c i -> fi)
  where
    desugarN f = desugarN . f . sugar
    sugarN   f = sugarN . f . desugar

--------------------------------------------------------------------------------

-- > SmartFunFull sym (a :-> b :-> ... :-> c) = ASTFull sym a -> ASTFull sym b -> ... -> ASTFull sym c
type family   SmartFull (sym :: * -> *) sig
type instance SmartFull sym (Full a)    = ASTFull sym a
type instance SmartFull sym (a :-> sig) = ASTFull sym a -> SmartFull sym sig

-- > S.SmartSig (ASTF sym a -> ASTF sym b -> ... -> ASTF sym c) = a :-> b :-> ... :-> c
-- > family   S.SmartSig f
type instance S.SmartSig (ASTFull sym sig)      = Full sig
type instance S.SmartSig (ASTFull sym sig -> f) = sig :-> S.SmartSig f

-- > family   S.SmartSym f :: * -> *
type instance S.SmartSym (ASTFull sym sig) = sym

sugarSymDecor
  :: ( Signature sig
     , f              ~ SmartFull  (sup :&: info) sig
     , fi             ~ S.SmartFun (sup :&: info) sig
     , sig            ~ S.SmartSig fi
     , (sup :&: info) ~ S.SmartSym fi
     , sub :<: sup
     , S.SyntacticN f fi
     )
  => info (S.DenResult sig) -> sub sig -> f
sugarSymDecor = S.sugarSymDecor

--------------------------------------------------------------------------------
-}
