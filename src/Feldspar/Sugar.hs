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

-- | Domains that support tuple expressions.
class Tuples dom
  where
    pair
      :: ( Type (PredicateOf dom) a
         , Type (PredicateOf dom) b
         , SyntacticN f (ASTF dom a -> ASTF dom b -> ASTF dom (a, b))
         )
      => f

    first
      :: ( Type (PredicateOf dom) a
         , SyntacticN f (ASTF dom (a, b) -> ASTF dom a)
         )
      => f

    second
      :: ( Type (PredicateOf dom) b
         , SyntacticN f (ASTF dom (a, b) -> ASTF dom b)
         )
      => f

--------------------------------------------------------------------------------

instance
    ( Syntactic a, Type (PredicateOf (Domain a)) (Internal a)
    , Syntactic b, Type (PredicateOf (Domain b)) (Internal b)
    , Domain a ~ Domain b
    , Tuples (Domain a)
    )
    => Syntactic (a, b)
  where
    type Domain   (a, b) = Domain a
    type Internal (a, b) = (Internal a, Internal b)

    desugar (a, b) = pair (desugar a) (desugar b)
    sugar   ab     = (first ab, second ab)

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
    sugar   = error "sugar not implemented for (a -> b)"
{-
    desugar = lamT_template varSym lamSym (desugar . f . sugar)
      where
        varSym v = inj (VarT v) :&: ValT typeRep
        lamSym v = Sym (inj (LamT v) :&: FunT typeRep (getDecor b)) :$ b
-}

--------------------------------------------------------------------------------
