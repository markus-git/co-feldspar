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
    compileType _ (v :: proxy a) =
      compTypeSign (hardwareRep :: HardwarePrimTypeRep a)    
    compileLit _ a = case hardwarePrimTypeOf a of
      BoolHT   -> literal a
      Int8HT   -> literal a
      Int16HT  -> literal a
      Int32HT  -> literal a
      Int64HT  -> literal a
      Word8HT  -> literal a
      Word16HT -> literal a
      Word32HT -> literal a
      Word64HT -> literal a

--------------------------------------------------------------------------------

instance CompileExp Prim
  where
    compE = compPrim

--------------------------------------------------------------------------------

compTypeSize :: forall a . HardwarePrimTypeRep a -> VHDL.Primary
compTypeSize Int8HT   = VHDL.lit $ show (8  :: Int)
compTypeSize Int16HT  = VHDL.lit $ show (16 :: Int)
compTypeSize Int32HT  = VHDL.lit $ show (32 :: Int)
compTypeSize Int64HT  = VHDL.lit $ show (64 :: Int)
compTypeSize Word8HT  = VHDL.lit $ show (8  :: Int)
compTypeSize Word16HT = VHDL.lit $ show (16 :: Int)
compTypeSize Word32HT = VHDL.lit $ show (32 :: Int)
compTypeSize Word64HT = VHDL.lit $ show (64 :: Int)

compTypeSign :: forall a. HardwarePrimTypeRep a -> VHDL VHDL.Type
compTypeSign BoolHT   = declare (Proxy :: Proxy a)
compTypeSign Int8HT   = declare (Proxy :: Proxy a)
compTypeSign Int16HT  = declare (Proxy :: Proxy a)
compTypeSign Int32HT  = declare (Proxy :: Proxy a)
compTypeSign Int64HT  = declare (Proxy :: Proxy a)
compTypeSign Word8HT  = declare (Proxy :: Proxy a)
compTypeSign Word16HT = declare (Proxy :: Proxy a)
compTypeSign Word32HT = declare (Proxy :: Proxy a)
compTypeSign Word64HT = declare (Proxy :: Proxy a)

--------------------------------------------------------------------------------

compExpr   :: [ASTF HardwarePrimDomain a] -> ([VHDL.Relation] -> VHDL.Expression) -> VHDL Kind
compExpr as f = do
  as' <- mapM compKind as
  return $ Hoist.E $ f $ map lift as'

compRel    :: [ASTF HardwarePrimDomain a] -> ([VHDL.ShiftExpression] -> VHDL.Relation) -> VHDL Kind
compRel as f = do
  as' <- mapM compKind as
  return $ Hoist.R $ f $ map lift as'

compShift :: ASTF HardwarePrimDomain a -> ASTF HardwarePrimDomain b -> (VHDL.SimpleExpression -> VHDL.SimpleExpression -> VHDL.ShiftExpression) -> VHDL Kind
compShift a b f = do
  a' <- compKind a
  b' <- compKind b
  return $ Hoist.Sh $ f (lift a') (lift b')

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

compCast :: forall a b . HardwarePrimTypeRep a -> ASTF HardwarePrimDomain b -> VHDL Kind
compCast t a = do
  let size = compTypeSize t
  t1   <- compTypeSign $ t
  t2   <- compTypeSign $ getDecor a
  a'   <- compKind a
  return $ Hoist.P $ VHDL.cast t1 $ lift $
    VHDL.resize (lift $ VHDL.cast t2 $ lift a')
                (lift size)

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

    go t I2N (a :* Nil) = compCast t a
    
    go _ Not (a :* Nil)      = compFactor [a]    (one VHDL.not)
    go _ And (a :* b :* Nil) = compExpr   [a, b] (    VHDL.and)
    go _ Eq  (a :* b :* Nil) = compRel    [a, b] (two VHDL.eq)
    go _ Lt  (a :* b :* Nil) = compRel    [a, b] (two VHDL.lt)
    go _ Lte (a :* b :* Nil) = compRel    [a, b] (two VHDL.lte)
    go _ Gt  (a :* b :* Nil) = compRel    [a, b] (two VHDL.gt)
    go _ Gte (a :* b :* Nil) = compRel    [a, b] (two VHDL.gte)

    go _ BitAnd   (a :* b :* Nil) = compExpr   [a, b] (    VHDL.and)
    go _ BitOr    (a :* b :* Nil) = compExpr   [a, b] (    VHDL.or)
    go _ BitXor   (a :* b :* Nil) = compExpr   [a, b] (    VHDL.xor)
    go _ BitCompl (a :* Nil)      = compFactor [a]    (one VHDL.not)
    
    go _ ShiftL  (a :* b :* Nil) = compShift a b VHDL.sll
    go _ ShiftR  (a :* b :* Nil) = compShift a b VHDL.srl
    go _ RotateL (a :* b :* Nil) = compShift a b VHDL.rol
    go _ RotateR (a :* b :* Nil) = compShift a b VHDL.ror

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
