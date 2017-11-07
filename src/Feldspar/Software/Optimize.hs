{-# language GADTs            #-}
{-# language TypeOperators    #-}
{-# language PatternSynonyms  #-}
{-# language ViewPatterns     #-}
{-# language FlexibleContexts #-}

module Feldspar.Software.Optimize where

import Feldspar.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression

import Data.Struct
import Data.Selection

import Control.Monad.Reader
import Control.Monad.Writer hiding (Any (..))
import Data.Maybe
import Data.Constraint (Dict (..))
import Data.Set (Set)

import qualified Data.Monoid as Monoid
import qualified Data.Set as Set

-- syntactic.
import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple
import Language.Syntactic.Functional.Sharing


--------------------------------------------------------------------------------
-- * Optimize software expressions.
--------------------------------------------------------------------------------

viewLit :: ASTF SoftwareDomain a -> Maybe a
viewLit lit | Just (Lit a) <- prj lit = Just a
viewLit _ = Nothing

witInteger :: ASTF SoftwareDomain a -> Maybe (Dict (Integral a, Ord a))
witInteger a = case getDecor a of
  ValT (Node Int8ST)   -> Just Dict
  ValT (Node Int16ST)  -> Just Dict
  ValT (Node Int32ST)  -> Just Dict
  ValT (Node Int64ST)  -> Just Dict
  ValT (Node Word8ST)  -> Just Dict
  ValT (Node Word16ST) -> Just Dict
  ValT (Node Word32ST) -> Just Dict
  ValT (Node Word64ST) -> Just Dict
  _ -> Nothing

isExact :: ASTF SoftwareDomain a -> Bool
isExact = isJust . witInteger

-- | projection with a stronger constraint to allow using it in
--   bidirectional patterns.
prjBi :: (sub :<: sup) => sup sig -> Maybe (sub sig)
prjBi = prj


--------------------------------------------------------------------------------

pattern SymP t s <- Sym ((prjBi -> Just s) :&: ValT t)
  where
    SymP t s = Sym ((inj s) :&: ValT t)

pattern VarP t v <- Sym ((prjBi -> Just (VarT v)) :&: t)
  where
    VarP t v = Sym (inj (VarT v) :&: t)

pattern LamP t v body <- Sym ((prjBi -> Just (LamT v)) :&: t) :$ body
  where
    LamP t v body = Sym (inj (LamT v) :&: t) :$ body


--------------------------------------------------------------------------------

pattern LitP :: () => (Eq a, Show a)
  => STypeRep a -> a -> ASTF SoftwareDomain a
  
pattern AddP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern SubP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern MulP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern NegP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a

pattern DivP :: () => (Integral a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern ModP :: () => (Integral a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

--------------------------------------------------------------------------------

pattern NonLitP <- (viewLit -> Nothing)

pattern LitP t a <- Sym ((prj -> Just (Lit a)) :&: ValT t)
  where
    LitP t a = Sym (inj (Lit a) :&: ValT t)

pattern AddP t a b <- SymP t Add :$ a :$ b
  where
    AddP t a b = simplifyUp $ SymP t Add :$ a :$ b
  
pattern SubP t a b <- SymP t Sub :$ a :$ b
  where
    SubP t a b = simplifyUp $ SymP t Sub :$ a :$ b

pattern MulP t a b <- SymP t Mul :$ a :$ b
  where
    MulP t a b = simplifyUp $ SymP t Mul :$ a :$ b

pattern NegP t a <- SymP t Neg :$ a
  where
    NegP t a = simplifyUp $ SymP t Neg :$ a

pattern DivP t a b <- SymP t Div :$ a :$ b
  where
    DivP t a b = simplifyUp $ SymP t Div :$ a :$ b

pattern ModP t a b <- SymP t Mod :$ a :$ b
  where
    ModP t a b = simplifyUp $ SymP t Mod :$ a :$ b

--------------------------------------------------------------------------------

simplifyUp :: ASTF SoftwareDomain a -> ASTF SoftwareDomain a
-- Addition with zero.
simplifyUp (AddP t (LitP _ 0) b) | isExact b = b
simplifyUp (AddP t a (LitP _ 0)) | isExact a = a
-- Simplify additions with literals.
simplifyUp (AddP t (AddP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (b+c))
simplifyUp (AddP t (SubP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (c-b))
simplifyUp (AddP t a (LitP _ b)) | Just Dict <- witInteger a, b < 0
  = SubP t a (LitP t (negate b))
-- Subtraction with zero.
simplifyUp (SubP t (LitP _ 0) b) | isExact b = NegP t b
simplifyUp (SubP t a (LitP _ 0)) | isExact a = a
-- Simplify subtractions with literals.
simplifyUp (SubP t (AddP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (b-c))
simplifyUp (SubP t (SubP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = SubP t a (LitP t (b+c))
simplifyUp (SubP t a (LitP _ b)) | Just Dict <- witInteger a, b < 0
  = AddP t a (LitP t (negate b))
-- Multiplication with zero.
simplifyUp (MulP t (LitP _ 0) b) | isExact b = LitP t 0
simplifyUp (MulP t a (LitP _ 0)) | isExact a = LitP t 0
-- Multiplication with one.
simplifyUp (MulP t (LitP _ 1) b) | isExact b = b
simplifyUp (MulP t a (LitP _ 1)) | isExact a = a
-- Simplify multiplications with literals.
simplifyUp (MulP t (MulP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = MulP t a (LitP t (b*c))
-- Simplify negations.
simplifyUp (NegP t (NegP _ a))   | isExact a = a
simplifyUp (NegP t (AddP _ a b)) | isExact a = SubP t (NegP t a) b
simplifyUp (NegP t (SubP _ a b)) | isExact a = SubP t b a
simplifyUp (NegP t (MulP _ a b)) | isExact a = MulP t a (NegP t b)
-- Move literals to the right.
simplifyUp (AddP t a@(LitP _ _) b@NonLitP) | isExact a = AddP t b a
simplifyUp (SubP t a@(LitP _ _) b@NonLitP) | isExact a = AddP t (NegP t b) a
simplifyUp (MulP t a@(LitP _ _) b@NonLitP) | isExact a = MulP t b a
-- Simplify not-expressions.
-- Not sure (yet) why I can't write `simplifyUp (NotP _ (NotP _ a)) = a`
simplifyUp (SymP _ Not :$ (SymP _ Not :$ a)) = a
simplifyUp (SymP t Not :$ (SymP _ Lt :$ a :$ b))
  = simplifyUp $ SymP t Gte :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Gt :$ a :$ b))
  = simplifyUp $ SymP t Lte :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Lte :$ a :$ b))
  = simplifyUp $ SymP t Gt :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Gte :$ a :$ b))
  = simplifyUp $ SymP t Lt :$ a :$ b
-- Simplify and-expressions.
simplifyUp (SymP _ And :$ LitP t False :$ _) = LitP t False
simplifyUp (SymP _ And :$ _ :$ LitP t False) = LitP t False
simplifyUp (SymP _ And :$ LitP t True :$ b)  = b
simplifyUp (SymP _ And :$ a :$ LitP t True)  = a
-- Simplify or-expressions.
simplifyUp (SymP _ Or :$ LitP t False :$ b) = b
simplifyUp (SymP _ Or :$ a :$ LitP t False) = a
simplifyUp (SymP _ Or :$ LitP t True :$ _)  = LitP t True
simplifyUp (SymP _ Or :$ _ :$ LitP t True)  = LitP t True
-- Simplify conditional expressions.
simplifyUp (SymP _ Cond :$ LitP _ True  :$ t :$ _)  = t
simplifyUp (SymP _ Cond :$ LitP _ False :$ _ :$ f)  = f
--simplifyUp (SymP _ Cond :$ c :$ t :$ f) | equal t f = t


--------------------------------------------------------------------------------
