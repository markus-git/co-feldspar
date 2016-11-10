{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Hardware.Compile (compile, icompile) where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Hardware.Primitive
import Feldspar.Hardware.Primitive.Backend
import Feldspar.Hardware.Representation

import Data.Struct

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Constraint hiding (Sub)
import Data.Map (Map)
import qualified Data.Map as Map

-- operational-higher.
import Control.Monad.Operational.Higher (Program, ProgramT)
import qualified Control.Monad.Operational.Higher as Oper

-- syntactic.
import Language.Syntactic --(AST (..), ASTF (..), (:&:) (..), Args (..), prj)
import Language.Syntactic.Functional hiding (Binding (..))
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as S

-- hardware-edsl.
import Language.Embedded.Hardware hiding (Hardware, HExp, Name, compile, icompile)
import qualified Language.Embedded.Hardware         as Hard
import qualified Language.Embedded.Hardware.Command as Hard

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Struct expression.
type VExp = Struct HardwarePrimType Prim

-- | Struct expression with hidden result type.
data VExp' where
  VExp' :: Struct HardwarePrimType Prim a -> VExp'

newRefV :: Monad m => HTypeRep a -> String -> TargetT m (Struct HardwarePrimType Hard.Variable a)
newRefV t base = lift $ mapStructA (const (Hard.newNamedVariable base)) t

initRefV :: Monad m => String -> VExp a -> TargetT m (Struct HardwarePrimType Hard.Variable a)
initRefV base = lift . mapStructA (Hard.initNamedVariable base)

getRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> TargetT m (VExp a)
getRefV = lift . mapStructA Hard.getVariable

setRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> VExp a -> TargetT m ()
setRefV r = lift . sequence_ . zipListStruct Hard.setVariable r

unsafeFreezeRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> TargetT m (VExp a)
unsafeFreezeRefV = lift . mapStructA unsafeFreezeVariable

--------------------------------------------------------------------------------

type Env = Map Name VExp'

localAlias :: MonadReader Env m => Name -> VExp a -> m b -> m b
localAlias v e = local (Map.insert v (VExp' e))

lookAlias :: MonadReader Env m => HTypeRep a -> Name -> m (VExp a)
lookAlias t v = do
  env <- ask
  return $ case Map.lookup v env of
    Nothing -> error $ "lookAlias: variable " ++ show v ++ " not in scope."
    Just (VExp' e) -> case hardwareTypeEq t (hardwareTypeRep e) of Just Dict -> e

--------------------------------------------------------------------------------

type TargetCMD
    =        Hard.VariableCMD
    Oper.:+: Hard.ArrayCMD
    Oper.:+: Hard.VArrayCMD
    Oper.:+: Hard.LoopCMD
    Oper.:+: Hard.ConditionalCMD
    Oper.:+: Hard.ComponentCMD
    Oper.:+: Hard.StructuralCMD
    Oper.:+: Hard.ConstantCMD
    Oper.:+: Hard.SignalCMD

type TargetT m = ReaderT Env (ProgramT TargetCMD (Oper.Param2 Prim HardwarePrimType) m)

type ProgH = Program TargetCMD (Oper.Param2 Prim HardwarePrimType)

--------------------------------------------------------------------------------

translateExp :: forall m a . Monad m => HExp a -> TargetT m (VExp a)
translateExp = goAST . unHExp
  where
    goAST :: ASTF HardwareDomain b -> TargetT m (VExp b)
    goAST = simpleMatch (\(s :&: ValT t) -> go t s)

    goSmallAST :: HardwarePrimType b => S.ASTF HardwareDomain b -> TargetT m (Prim b)
    goSmallAST = fmap extractNode . goAST

    go    :: HTypeRep (DenResult sig)
          -> HardwareConstructs sig
          -> Args (AST HardwareDomain) sig
          -> TargetT m (VExp (DenResult sig))
    go t lit Nil
      | Just (Lit a) <- prj lit
      = return $ mapStruct (litE . runIdentity) $ toStruct t a
    go t lit Nil
      | Just (Literal a) <- prj lit
      = return $ mapStruct (litE . runIdentity) $ toStruct t a
    go t var Nil
      | Just (FreeVar v) <- prj var
      = return $ Node $ sugarSymPrim $ FreeVar v
    go t var Nil
      | Just (VarT v) <- prj var
      = lookAlias t v
    go t lt (a :* (lam :$ body) :* Nil)
      | Just (Let tag) <- prj lt
      , Just (LamT v)  <- prj lam
      = do let base = if Prelude.null tag then "let" else tag
           r  <- initRefV base =<< goAST a
           a' <- unsafeFreezeRefV r
           localAlias v a' $ goAST body
    go t tup (a :* b :* Nil)
      | Just Pair <- prj tup
      = Branch <$> goAST a <*> goAST b
    go t sel (ab :* Nil)
      | Just Fst <- prj sel
      = do Branch a _ <- goAST ab
           return a
      | Just Snd <- prj sel
      = do Branch _ b <- goAST ab
           return b
    go t op (a :* Nil)
      | Just Neg <- prj op = liftStruct (sugarSymPrim Neg) <$> goAST a
      | Just Not <- prj op = liftStruct (sugarSymPrim Not) <$> goAST a
    go t op (a :* b :* Nil)
      | Just Add <- prj op = liftStruct2 (sugarSymPrim Add) <$> goAST a <*> goAST b
      | Just Sub <- prj op = liftStruct2 (sugarSymPrim Sub) <$> goAST a <*> goAST b
      | Just Mul <- prj op = liftStruct2 (sugarSymPrim Mul) <$> goAST a <*> goAST b
      | Just Div <- prj op = liftStruct2 (sugarSymPrim Div) <$> goAST a <*> goAST b
      | Just And <- prj op = liftStruct2 (sugarSymPrim And) <$> goAST a <*> goAST b
      | Just Eq  <- prj op = liftStruct2 (sugarSymPrim Eq)  <$> goAST a <*> goAST b
      | Just Lt  <- prj op = liftStruct2 (sugarSymPrim Lt)  <$> goAST a <*> goAST b
    go _ arrIx (i :* Nil)
      | Just (ArrIx arr) <- prj arrIx
      = do i' <- goSmallAST i
           return $ Node $ sugarSymPrim (ArrIx arr) i'
    go _ s _ = error $ "hardware translation handling for symbol " ++ S.renderSym s ++ " is missing."

--------------------------------------------------------------------------------

unsafeTranslateSmallExp :: Monad m => HExp a -> TargetT m (Prim a)
unsafeTranslateSmallExp a =
  do Node b <- translateExp a
     return b

--------------------------------------------------------------------------------

translate :: Hardware a -> ProgH a
translate = flip runReaderT Map.empty . Oper.reexpressEnv unsafeTranslateSmallExp . unHardware

--------------------------------------------------------------------------------

compile :: Hardware a -> String
compile = Hard.compile . translate

icompile :: Hardware a -> IO ()
icompile = Hard.icompile . translate

--------------------------------------------------------------------------------
