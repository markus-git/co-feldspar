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

import Control.Monad.Operational.Higher (Program, ProgramT)
import qualified Control.Monad.Operational.Higher as Oper

-- syntactic.
import Language.Syntactic --(AST (..), ASTF (..), (:&:) (..), Args (..), prj)
import Language.Syntactic.Functional hiding (Binding (..))
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as S

-- imperative-edsl.
import qualified Language.Embedded.Imperative     as Soft
import qualified Language.Embedded.Imperative.CMD as Soft
import qualified Language.Embedded.Expression     as Soft

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

newRefV :: Monad m => HTypeRep a -> String -> InterT m (Struct HardwarePrimType Hard.Variable a)
newRefV t base = lift $ mapStructA (const (Hard.newNamedVariable base)) t

initRefV :: Monad m => String -> VExp a -> InterT m (Struct HardwarePrimType Hard.Variable a)
initRefV base = lift . mapStructA (Hard.initNamedVariable base)

getRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> InterT m (VExp a)
getRefV = lift . mapStructA Hard.getVariable

setRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> VExp a -> InterT m ()
setRefV r = lift . sequence_ . zipListStruct Hard.setVariable r

unsafeFreezeRefV :: Monad m => Struct HardwarePrimType Hard.Variable a -> InterT m (VExp a)
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

type InterCMD
    =        Hard.VariableCMD
    Oper.:+: Hard.ArrayCMD
    Oper.:+: Hard.VArrayCMD
    Oper.:+: Hard.LoopCMD
    Oper.:+: Hard.ConditionalCMD
    Oper.:+: Hard.ComponentCMD
    Oper.:+: Hard.StructuralCMD
    Oper.:+: Hard.ConstantCMD
    Oper.:+: Hard.SignalCMD
    -- leftovers from using imperative-edsl instructions for comp.
    Oper.:+: Soft.RefCMD
    Oper.:+: Soft.ArrCMD
    Oper.:+: Soft.ControlCMD

-- | Inter monad for intermediate translations.
type InterT m = ReaderT Env (ProgramT InterCMD (Oper.Param2 Prim HardwarePrimType) m)

--------------------------------------------------------------------------------

translateExp :: forall m a . Monad m => HExp a -> InterT m (VExp a)
translateExp = goAST . unHExp
  where
    goAST :: ASTF HardwareDomain b -> InterT m (VExp b)
    goAST = simpleMatch (\(s :&: ValT t) -> go t s)

    go    :: HTypeRep (DenResult sig)
          -> HardwareConstructs sig
          -> Args (AST HardwareDomain) sig
          -> InterT m (VExp (DenResult sig))
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
    go _ s _ = error $ "hardware translation handling for symbol " ++ S.renderSym s ++ " is missing."

--------------------------------------------------------------------------------

unsafeTranslateSmallExp :: Monad m => HExp a -> InterT m (Prim a)
unsafeTranslateSmallExp a =
  do Node b <- translateExp a
     return b

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

class Lower instr
  where
    lower :: instr (Oper.Param3 ProgH Prim HardwarePrimType) a -> ProgH a

instance (Lower i, Lower j) => Lower (i Oper.:+: j)
  where
    lower (Oper.Inl i) = lower i
    lower (Oper.Inr j) = lower j

instance Lower Soft.RefCMD
  where
    lower (Soft.NewRef n)    = v2r <$> Hard.newNamedVariable n
    lower (Soft.InitRef n e) = v2r <$> Hard.initNamedVariable n e
    lower (Soft.GetRef r)    = soften <$> Oper.singleInj (Hard.GetVariable (r2v r))
    lower (Soft.SetRef r e)  = Hard.setVariable (r2v r) e

instance Lower Soft.ArrCMD
  where
    lower (Soft.NewArr n e)    = v2a <$> Oper.singleInj (Hard.NewVArray (Hard.Base n) e)
    lower (Soft.ConstArr n es) = v2a <$> Oper.singleInj (Hard.InitVArray (Hard.Base n) es)
    lower (Soft.GetArr a i)    = soften <$> Oper.singleInj (Hard.GetVArray i (a2v a))
    lower (Soft.SetArr a i e)  = Oper.singleInj (Hard.SetVArray i e (a2v a))
    lower _ = error "todo: lower missing cases for arrays."

instance Lower Soft.ControlCMD
  where
    lower (Soft.If b tru fls)       = Oper.singleInj (Hard.If (b, tru) [] (Just fls))
    lower (Soft.While cont body)    = Oper.singleInj (Hard.While cont body)
    lower (Soft.For (_, _, b) body) = Oper.singleInj (Hard.For (Soft.borderVal b) (body . soften))
    lower _ = error "todo: lower missing cases for control."

instance Lower Hard.VariableCMD    where lower = Oper.singleInj
instance Lower Hard.ArrayCMD       where lower = Oper.singleInj
instance Lower Hard.VArrayCMD      where lower = Oper.singleInj
instance Lower Hard.ComponentCMD   where lower = Oper.singleInj
instance Lower Hard.StructuralCMD  where lower = Oper.singleInj
instance Lower Hard.SignalCMD      where lower = Oper.singleInj
instance Lower Hard.ConstantCMD    where lower = Oper.singleInj
instance Lower Hard.LoopCMD        where lower = Oper.singleInj
instance Lower Hard.ConditionalCMD where lower = Oper.singleInj

--------------------------------------------------------------------------------

translate :: Hardware a -> ProgH a
translate =
    -- translate shared instructions.
    Oper.interpretWithMonad lower
    -- fuse the program stack
  . Oper.interpretWithMonadT Oper.singleton id
    -- compile outer program.
  . flip runReaderT Map.empty . Oper.reexpressEnv unsafeTranslateSmallExp
    -- compile inner program.
  . Oper.interpretWithMonadT Oper.singleton
      (lift . flip runReaderT Map.empty . Oper.reexpressEnv unsafeTranslateSmallExp)
    -- open program stack.
  . unHardware

--------------------------------------------------------------------------------

compile :: Hardware a -> String
compile = Hard.compile . translate

icompile :: Hardware a -> IO ()
icompile = Hard.icompile . translate

--------------------------------------------------------------------------------

soften :: Hard.Val a -> Soft.Val a
soften (Hard.ValC i) = Soft.ValComp i
soften (Hard.ValE v) = Soft.ValRun  v

harden :: Soft.Val a -> Hard.Val a
harden (Soft.ValComp i) = Hard.ValC i
harden (Soft.ValRun  v) = Hard.ValE v

--------------------------------------------------------------------------------

v2r :: Hard.Variable a -> Soft.Ref a
v2r (Hard.VariableC i) = Soft.RefComp i
v2r (Hard.VariableE v) = Soft.RefRun  v

r2v :: Soft.Ref a -> Hard.Variable a
r2v (Soft.RefComp i) = Hard.VariableC i
r2v (Soft.RefRun  v) = Hard.VariableE v

--------------------------------------------------------------------------------

a2v :: Soft.Arr i a -> Hard.VArray i a
a2v (Soft.ArrComp i) = Hard.VArrayC i
a2v (Soft.ArrRun  v) = Hard.VArrayE v

v2a :: Hard.VArray i a -> Soft.Arr i a
v2a (Hard.VArrayC i) = Soft.ArrComp i
v2a (Hard.VArrayE v) = Soft.ArrRun  v

--------------------------------------------------------------------------------
