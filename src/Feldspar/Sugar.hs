{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
-- todo : is this bad? comes from how I use `sup` in the `Syntactic`
--        instance for pairs.
{-# language UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Feldspar.Sugar where

import Feldspar.Representation
import Data.Struct

import Data.Constraint (Constraint)
import Data.Typeable (Typeable)
import Data.Proxy (Proxy(..))

import qualified Language.Haskell.TH as TH

-- syntactic.
import Language.Syntactic
import Language.Syntactic.TH
import Language.Syntactic.Syntax
import Language.Syntactic.Sugar
import Language.Syntactic.Decoration
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple

--------------------------------------------------------------------------------
-- ** Tuples.
--------------------------------------------------------------------------------

-- | Domains that support tuple expressions.
class Tuples dom
  where
    pair   :: ( Type (Pred dom) a
              , Type (Pred dom) b
              , SyntacticN f (ASTF dom a -> ASTF dom b -> ASTF dom (a, b)))
           => f
    first  :: ( Type (Pred dom) a
              , SyntacticN f (ASTF dom (a, b) -> ASTF dom a))
           => f
    second :: ( Type (Pred dom) b
              , SyntacticN f (ASTF dom (a, b) -> ASTF dom b))
           => f

instance
    ( Syntactic a, Type (Pred (Domain a)) (Internal a)
    , Syntactic b, Type (Pred (Domain b)) (Internal b)
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
-- ** Functions.
--------------------------------------------------------------------------------

-- *** todo: replace current fix with comments once DTC bug is fixed.
instance
    ( Syntactic a
    , Syntactic b
--    , Domain a ~ (expr :&: TypeRepF pred (RepresentationOf pred))
--    , Domain b ~ (expr :&: TypeRepF pred (RepresentationOf pred))
    , (Domain a) ~ ((BindingT :+: sym) :&: TypeRepF pred (RepresentationOf pred))
    , (Domain b) ~ ((BindingT :+: sym) :&: TypeRepF pred (RepresentationOf pred))
--    , BindingT :<: expr
    , Type pred (Internal a)
    )
    => Syntactic (a -> b)
  where
    type Domain   (a -> b) = Domain a
    type Internal (a -> b) = Internal a -> Internal b

    desugar f = bepa varSym lamSym (desugar . f . sugar)
--                lamT_template varSym lamSym (desugar . f . sugar)
      where
--        varSym v   = inj (VarT v) :&: ValT typeRep
--        lamSym v b = Sym (inj (LamT v) :&: FunT typeRep (getDecor b)) :$ b
        varSym v   = InjL (VarT v) :&: ValT typeRep
        lamSym v b = Sym (InjL (LamT v) :&: FunT typeRep (getDecor b)) :$ b

    sugar = error "sugar not implemented for (a -> b)"

--------------------------------------------------------------------------------

apa :: (sym ~ ((BindingT :+: sym0) :&: decor)) => AST sym a -> Name
apa (Sym ((InjL (LamT n)) :&: _) :$ _) = n
apa (s :$ a) = apa s `Prelude.max` apa a
apa _ = 0

bepa :: (sym ~ ((BindingT :+: sym0) :&: decor))
  => (Name -> sym (Full a))
  -> (Name -> ASTF sym b -> ASTF sym (a -> b))
  -> (ASTF sym a -> ASTF sym b) -> ASTF sym (a -> b)
bepa mkVar mkLam f = mkLam v body
  where
    body = f $ Sym $ mkVar v
    v    = succ $ apa body

--------------------------------------------------------------------------------
