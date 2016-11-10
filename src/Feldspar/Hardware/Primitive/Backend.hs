{-# language GADTs #-}
{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

module Feldspar.Hardware.Primitive.Backend where

import Feldspar.Hardware.Primitive

import Data.Constraint (Dict(..))
import Data.Proxy

-- syntactic.
import Language.Syntactic

-- hardware-edsl.
import Language.Embedded.Hardware
import Language.Embedded.Hardware.Expression.Represent
import Language.Embedded.Hardware.Expression.Hoist (lift, Kind)
import Language.Embedded.Hardware.Command.CMD (IArray(..))
import qualified Language.Embedded.Hardware.Expression.Hoist as Hoist

import Language.Embedded.VHDL (VHDL)
import qualified Language.VHDL          as VHDL
import qualified Language.Embedded.VHDL as VHDL

--------------------------------------------------------------------------------
-- * Compilation of hardware primitives.
--------------------------------------------------------------------------------

viewLitPrim :: ASTF HardwarePrimDomain a -> Maybe a
viewLitPrim (Sym (Lit a :&: _ )) = Just a
viewLitPrim _                    = Nothing

--------------------------------------------------------------------------------

instance CompileType HardwarePrimType
  where
    compileType _ (v :: proxy a) = case hardwareRep :: HardwarePrimTypeRep a of
      BoolHT  -> declare v
      Int8HT  -> declare v
      Word8HT -> declare v
    
    compileLit _ a = case hardwarePrimTypeOf a of
      BoolHT  -> literal a
      Int8HT  -> literal a
      Word8HT -> literal a

--------------------------------------------------------------------------------

instance CompileExp Prim
  where
    compE = compPrim

--------------------------------------------------------------------------------

compExpr   :: [ASTF HardwarePrimDomain a] -> ([VHDL.Relation] -> VHDL.Expression) -> VHDL Kind
compExpr as f = do
  as' <- mapM compKind as
  return $ Hoist.E $ f $ map lift as'

compRel    :: [ASTF HardwarePrimDomain a] -> ([VHDL.ShiftExpression] -> VHDL.Relation) -> VHDL Kind
compRel as f = do
  as' <- mapM compKind as
  return $ Hoist.R $ f $ map lift as'

compSimple :: [ASTF HardwarePrimDomain a] -> ([VHDL.Term] -> VHDL.SimpleExpression) -> VHDL Kind
compSimple as f = do
  as' <- mapM compKind as
  return $ Hoist.Si $ f $ map lift as'

compTerm   :: [ASTF HardwarePrimDomain a] -> ([VHDL.Factor] -> VHDL.Term) -> VHDL Kind
compTerm as f = do
  as' <- mapM compKind as
  return $ Hoist.T $ f $ map lift as'

compFactor :: [ASTF HardwarePrimDomain a] -> ([VHDL.Primary] -> VHDL.Factor) -> VHDL Kind
compFactor as f = do
  as' <- mapM compKind as
  return $ Hoist.F $ f $ map lift as'

--------------------------------------------------------------------------------

compKind :: ASTF HardwarePrimDomain a -> VHDL Kind
compKind = simpleMatch (\(s :&: t) -> go t s)
  where
    go :: forall sig
        . HardwarePrimTypeRep (DenResult sig)
        -> HardwarePrimConstructs sig
        -> Args (AST HardwarePrimDomain) sig
        -> VHDL Kind
    go _ (FreeVar v) Nil =
      return $ Hoist.P $ VHDL.name $ VHDL.NSimple $ VHDL.Ident v
    go t (Lit a)     Nil | Dict <- hardwarePrimWitType t =
      fmap Hoist.E $ compileLit (Proxy :: Proxy HardwarePrimType) a
    go _ Neg (a :* Nil)      = compSimple [a]    (one VHDL.neg)
    go _ Add (a :* b :* Nil) = compSimple [a, b] VHDL.add
    go _ Sub (a :* b :* Nil) = compSimple [a, b] VHDL.sub
    go _ Mul (a :* b :* Nil) = compTerm   [a, b] VHDL.mul
    go _ Div (a :* b :* Nil) = compTerm   [a, b] VHDL.div
    go _ Mod (a :* b :* Nil) = compTerm   [a, b] VHDL.mod
    go _ Not (a :* Nil)      = compFactor [a]    (one VHDL.not)
    go _ And (a :* b :* Nil) = compExpr   [a, b] VHDL.and
    go _ Eq  (a :* b :* Nil) = compRel    [a, b] (two VHDL.eq)
    go _ Lt  (a :* b :* Nil) = compRel    [a, b] (two VHDL.lt)

    go _ (ArrIx (IArrayC arr)) (i :* Nil) =
      do i' <- compPrim $ Prim i
         return $ Hoist.P $ VHDL.name $ VHDL.indexed (VHDL.Ident arr) (lift i')

    one :: (a -> b) -> ([a] -> b)
    one f = \[a] -> f a

    two :: (a -> a -> b) -> ([a] -> b)
    two f = \[a, b] -> f a b
    
--------------------------------------------------------------------------------

compPrim :: Prim a -> VHDL VHDL.Expression
compPrim = fmap lift . compKind . unPrim

--------------------------------------------------------------------------------
