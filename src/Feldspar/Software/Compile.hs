{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Software.Compile where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Primitive.Backend
import Feldspar.Software.Representation

import Data.Struct

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Constraint hiding (Sub)
import Data.Map (Map)
import qualified Data.Map as Map

-- syntactic.
import Language.Syntactic (AST (..), (:&:) (..), Args (..), prj)
import Language.Syntactic.Functional hiding (Binding (..))
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as S

-- operational-higher.
import Control.Monad.Operational.Higher (Program)
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Expression
import Language.Embedded.Imperative hiding ((:+:)(..), (:<:)(..))
import Language.Embedded.Concurrent
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Backend.C  as Imp

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Struct expression.
type VExp = Struct SoftwarePrimType Prim

-- | Struct expression with hidden result type.
data VExp' where
  VExp' :: Struct SoftwarePrimType Prim a -> VExp'

newRefV :: Monad m => STypeRep a -> String -> TargetT m (Struct SoftwarePrimType Imp.Ref a)
newRefV t base = lift $ mapStructA (const (Imp.newNamedRef base)) t

initRefV :: Monad m => String -> VExp a -> TargetT m (Struct SoftwarePrimType Imp.Ref a)
initRefV base = lift . mapStructA (Imp.initNamedRef base)

getRefV :: Monad m => Struct SoftwarePrimType Imp.Ref a -> TargetT m (VExp a)
getRefV = lift . mapStructA Imp.getRef

setRefV :: Monad m => Struct SoftwarePrimType Imp.Ref a -> VExp a -> TargetT m ()
setRefV r = lift . sequence_ . zipListStruct Imp.setRef r

unsafeFreezeRefV :: Monad m => Struct SoftwarePrimType Imp.Ref a -> TargetT m (VExp a)
unsafeFreezeRefV = lift . mapStructA unsafeFreezeRef

--------------------------------------------------------------------------------

type Env = Map Name VExp'

localAlias :: MonadReader Env m => Name -> VExp a -> m b -> m b
localAlias v e = local (Map.insert v (VExp' e))

lookAlias :: MonadReader Env m => STypeRep a -> Name -> m (VExp a)
lookAlias t v = do
  env <- ask
  return $ case Map.lookup v env of
    Nothing -> error $ "lookAlias: variable " ++ show v ++ " not in scope."
    Just (VExp' e) -> case softwareTypeEq t (softwareTypeRep e) of Just Dict -> e

--------------------------------------------------------------------------------

type TargetCMD
    =        RefCMD
    Oper.:+: ArrCMD
    Oper.:+: ControlCMD
    Oper.:+: ThreadCMD
    Oper.:+: ChanCMD
    Oper.:+: PtrCMD
    Oper.:+: FileCMD
    Oper.:+: C_CMD

-- | Target monad during translation
type TargetT m = ReaderT Env (ProgramT TargetCMD (Oper.Param2 Prim SoftwarePrimType) m)

-- | Monad for translated program
type ProgC = Program TargetCMD (Oper.Param2 Prim SoftwarePrimType)

--------------------------------------------------------------------------------

translateExp :: forall m a . Monad m => SExp a -> TargetT m (VExp a)
translateExp = goAST . unSExp
  where
    goAST :: S.ASTF SoftwareDomain b -> TargetT m (VExp b)
    goAST = S.simpleMatch (\(s :&: ValT t) -> go t s)

    goSmallAST :: SoftwarePrimType b => S.ASTF SoftwareDomain b -> TargetT m (Prim b)
    goSmallAST = fmap extractNode . goAST

    go :: STypeRep (S.DenResult sig) 
       -> SoftwareConstructs sig
       -> S.Args (S.AST SoftwareDomain) sig
       -> TargetT m (VExp (S.DenResult sig))
    go t lit Nil
      | Just (Lit a) <- prj lit
      = return $ mapStruct (constExp . runIdentity) $ toStruct t a
    go t lit Nil
      | Just (Literal a) <- prj lit
      = return $ mapStruct (constExp . runIdentity) $ toStruct t a
    go t var Nil
      | Just (FreeVar v) <- prj var
      = return $ Node $ sugarSymPrim $ FreeVar v
    go t var Nil
      | Just (VarT v) <- prj var
      = lookAlias t v
    go t lt (a :* (lam :$ body) :* Nil)
      | Just (Let tag) <- prj lt
      , Just (LamT v)  <- prj lam
      = do let base = if null tag then "let" else tag
           r  <- initRefV base =<< goAST a
           a' <- unsafeFreezeRefV r
           localAlias v a' $ goAST body
    go t tup (a :* b :* Nil)
      | Just Pair <- prj tup
      = Branch <$> goAST a <*> goAST b
    go t sel (ab :* Nil)
      | Just Fst <- prj sel = do
          Branch a _ <- goAST ab
          return a
      | Just Snd <- prj sel = do
          Branch _ b <- goAST ab
          return b
    go _ op (a :* Nil)
      | Just Neg <- prj op = liftStruct (sugarSymPrim Neg) <$> goAST a
      | Just Not <- prj op = liftStruct (sugarSymPrim Not) <$> goAST a
      | Just Sin <- prj op = liftStruct (sugarSymPrim Sin) <$> goAST a
      | Just Cos <- prj op = liftStruct (sugarSymPrim Cos) <$> goAST a
      | Just Tan <- prj op = liftStruct (sugarSymPrim Tan) <$> goAST a
      | Just I2N <- prj op = liftStruct (sugarSymPrim I2N) <$> goAST a
      | Just BitCompl <- prj op =
          liftStruct (sugarSymPrim BitCompl) <$> goAST a
    go _ op (a :* b :* Nil)
      | Just Add <- prj op = liftStruct2 (sugarSymPrim Add) <$> goAST a <*> goAST b
      | Just Sub <- prj op = liftStruct2 (sugarSymPrim Sub) <$> goAST a <*> goAST b
      | Just Mul <- prj op = liftStruct2 (sugarSymPrim Mul) <$> goAST a <*> goAST b
      | Just Div <- prj op = liftStruct2 (sugarSymPrim Div) <$> goAST a <*> goAST b
      | Just Mod <- prj op = liftStruct2 (sugarSymPrim Mod) <$> goAST a <*> goAST b
      | Just Eq  <- prj op = liftStruct2 (sugarSymPrim Eq)  <$> goAST a <*> goAST b
      | Just Lt  <- prj op = liftStruct2 (sugarSymPrim Lt)  <$> goAST a <*> goAST b
      | Just BitAnd <- prj op =
          liftStruct2 (sugarSymPrim BitAnd) <$> goAST a <*> goAST b
      | Just BitOr  <- prj op =
          liftStruct2 (sugarSymPrim BitOr) <$> goAST a <*> goAST b
      | Just BitXor <- prj op =
          liftStruct2 (sugarSymPrim BitXor) <$> goAST a <*> goAST b
      | Just ShiftL <- prj op =
          liftStruct2 (sugarSymPrim ShiftL) <$> goAST a <*> goAST b
      | Just ShiftR <- prj op =
          liftStruct2 (sugarSymPrim ShiftR) <$> goAST a <*> goAST b
      | Just RotateL <- prj op =
          liftStruct2 (sugarSymPrim RotateL) <$> goAST a <*> goAST b
      | Just RotateR <- prj op =
          liftStruct2 (sugarSymPrim RotateR) <$> goAST a <*> goAST b
    go t loop (len :* init :* (lami :$ (lams :$ body)) :* Nil)
      | Just ForLoop   <- prj loop
      , Just (LamT iv) <- prj lami
      , Just (LamT sv) <- prj lams = do
          len'  <- goSmallAST len
          state <- initRefV "state" =<< goAST init
          ReaderT $ \env -> Imp.for (0, 1, Imp.Excl len') $ \i -> flip runReaderT env $ do
            s <- case t of
              Node _ -> unsafeFreezeRefV state
              _      -> getRefV state
            s' <- localAlias iv (Node i) $ localAlias sv s $ goAST body
            setRefV state s'
          unsafeFreezeRefV state
    go _ arrIx (i :* Nil)
      | Just (ArrIx arr) <- prj arrIx = do
          i' <- goSmallAST i
          return $ Node $ sugarSymPrim (ArrIx arr) i'
    go _ s _ = error $ "software translation handling for symbol " ++ S.renderSym s ++ " is missing."

--------------------------------------------------------------------------------

unsafeTranslateSmallExp :: Monad m => SExp a -> TargetT m (Prim a)
unsafeTranslateSmallExp a = do
  Node b <- translateExp a
  return b

--------------------------------------------------------------------------------

translate :: Software a -> ProgC a
translate = flip runReaderT Map.empty . Oper.reexpressEnv unsafeTranslateSmallExp . unSoftware

--------------------------------------------------------------------------------

compile :: Software a -> String
compile = Imp.compile . translate

icompile :: Software a -> IO ()
icompile = Imp.icompile . translate

--------------------------------------------------------------------------------
