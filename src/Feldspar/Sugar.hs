{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FunctionalDependencies #-}
{-# language UndecidableInstances #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}

module Feldspar.Sugar where

import Data.Constraint (Constraint)
import Data.Proxy (Proxy(..))
import Data.Struct

import Language.Syntactic.Syntax
import Language.Syntactic.Decoration

--------------------------------------------------------------------------------
-- * Sugaring of expressions.
--------------------------------------------------------------------------------

class Syntactic a
  where
    type Constructor a :: * -> *
    type Internal    a :: *

    desugar :: a -> Constructor a (Internal a)
    sugar   :: Constructor a (Internal a) -> a

--  trep    :: Proxy a -> Struct (PredOf (Constructor a)) (TypeOf a) (Internal a)

-- | Associate an expression type with its type constraint.
type family PredOf (c :: * -> *) :: (* -> Constraint)

-- | Syntactic type casting.
resugar :: (Syntactic a, Syntactic b, Constructor a ~ Constructor b, Internal a ~ Internal b) => a -> b
resugar = sugar . desugar

--------------------------------------------------------------------------------
-- ** Sugaring extended to functions.

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
-- ** Sugaring of symbols.

sugarSym
    :: ( Signature sig
       , fi  ~ SmartFun sup sig
       , sig ~ SmartSig fi
       , sup ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: sup
       )
    => sub sig -> f
sugarSym = sugarN . smartSym

sugarSymDecor
    :: ( Signature sig
       , fi             ~ SmartFun (sup :&: info) sig
       , sig            ~ SmartSig fi
       , (sup :&: info) ~ SmartSym fi
       , SyntacticN f fi
       , sub :<: sup
       )
    => info (DenResult sig) -> sub sig -> f
sugarSymDecor i = sugarN . smartSymDecor i

--------------------------------------------------------------------------------
