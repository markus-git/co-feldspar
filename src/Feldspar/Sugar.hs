{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}

-- todo : is this bad? comes from how I use `sup` in the `Syntactic` instance for pairs.
{-# language UndecidableInstances #-}

module Feldspar.Sugar where

import Feldspar.Representation

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

-- | Supported domain decorations.
class Decorated decor a
  where
    decorate :: decor a

-- | Representable types are decorated as fully applied types in `TypeRepF`.
instance (Type pred a, rep ~ Rep pred) => Decorated (TypeRepF pred rep) a
  where
    decorate = ValT typeRep

-- todo: functions over representable types.
--------------------------------------------------------------------------------

instance
    ( Syntactic a
    , Syntactic b
    )
    => Syntactic (a -> b)
  where
    type Domain   (a -> b) = Domain a
    type Internal (a -> b) = Internal a -> Internal b

    desugar = error "desugar not yet implemented for (a -> b)"
    sugar = error "sugar not implemented for (a -> b)"
{-
    desugar = lamT_template varSym lamSym (desugar . f . sugar)
      where
        varSym v = inj (VarT v) :&: ValT typeRep
        lamSym v = Sym (inj (LamT v) :&: FunT typeRep (getDecor b)) :$ b
-}

instance
    ( Syntactic a
    , Syntactic b
    , Domain b       ~ Domain a
    , (sup :&: info) ~ Domain a
    , Tuple :<: sup
      -- hmm... not that pretty.
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

-- Helper function for lifting a symbol's signature into a function:
--
-- > sugarSym... :: (Syntactic a,b,...,x , Domain a,b,...,x ~ (sup :&: info), Decorated info)
-- >   => sym (Internal a :-> Internal b :-> ... :-> Full (Internal x))
-- >   -> (a -> b -> ... -> x)
--
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
