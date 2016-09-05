{-# language TypeFamilies #-}
{-# language MultiParamTypeClasses #-}
{-# language FunctionalDependencies #-}
{-# language UndecidableInstances #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}
{-# language ScopedTypeVariables #-}
{-# language Rank2Types #-}

module Feldspar.Sugar where

import Data.Constraint (Constraint)
import Data.Proxy (Proxy(..))
import Data.Struct

import Language.Syntactic.Syntax as Syn
  ( AST(..), ASTFull(..), ASTF
  , Full(..), (:->)
  , Signature(..), SigRep(..)
  , (:+:), (:<:)
  , SmartSym, SmartSig, DenResult
  )
import Language.Syntactic.Decoration as Syn
  ((:&:))

import qualified Language.Syntactic.Syntax     as S
import qualified Language.Syntactic.Sugar      as S
import qualified Language.Syntactic.Decoration as S

--------------------------------------------------------------------------------
-- * Sugaring of expressions.
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
-- ** Smart constructors.

-- ...

--------------------------------------------------------------------------------
