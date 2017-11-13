{-# language GADTs               #-}
{-# language TypeOperators       #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Software.Compile where

import Feldspar.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Primitive.Backend
import Feldspar.Software.Expression
import Feldspar.Software.Representation
import Feldspar.Software.Optimize
import Data.Struct

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Proxy
import Data.Constraint hiding (Sub)
import Data.Map (Map)
import qualified Data.Map as Map

-- syntactic.
import Language.Syntactic (AST (..), ASTF, (:&:) (..), Args((:*)), prj)
import Language.Syntactic.Functional hiding (Binding (..))
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher (Program)
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Expression
import Language.Embedded.Imperative hiding (Ref, (:+:)(..), (:<:)(..))
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Backend.C  as Imp

-- debug.
import Debug.Trace

--------------------------------------------------------------------------------
-- * Software compiler.
--------------------------------------------------------------------------------

-- | Target software instructions.
type TargetCMD
    =        RefCMD
    Oper.:+: ArrCMD
    Oper.:+: ControlCMD
    Oper.:+: PtrCMD
    Oper.:+: FileCMD
    Oper.:+: C_CMD

-- | Target monad during translation.
type TargetT m = ReaderT Env (ProgramT TargetCMD (Oper.Param2 Prim SoftwarePrimType) m)

-- | Monad for translated programs.
type ProgC = Program TargetCMD (Oper.Param2 Prim SoftwarePrimType)

--------------------------------------------------------------------------------
-- ** Compilation of expressions.

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

translateExp :: forall m a . Monad m => SExp a -> TargetT m (VExp a)
translateExp = goAST . optimize . unSExp
  where
    goAST :: ASTF SoftwareDomain b -> TargetT m (VExp b)
    goAST = Syn.simpleMatch (\(s :&: ValT t) -> go t s)

    goSmallAST :: SoftwarePrimType b => ASTF SoftwareDomain b -> TargetT m (Prim b)
    goSmallAST = fmap extractNode . goAST

    go :: STypeRep (Syn.DenResult sig) 
       -> SoftwareConstructs sig
       -> Syn.Args (AST SoftwareDomain) sig
       -> TargetT m (VExp (Syn.DenResult sig))
    go t lit Syn.Nil
      | Just (Lit a) <- prj lit
      = return $ mapStruct (constExp . runIdentity) $ toStruct t a
    go t lit Syn.Nil
      | Just (Literal a) <- prj lit
      = return $ mapStruct (constExp . runIdentity) $ toStruct t a
    go t var Syn.Nil
      | Just (FreeVar v) <- prj var
      = return $ Node $ sugarSymPrim $ FreeVar v
    go t var Syn.Nil
      | Just (VarT v) <- prj var
      = do lookAlias t v
    go t lt (a :* (lam :$ body) :* Syn.Nil)
      | Just (Let tag) <- prj lt
      , Just (LamT v)  <- prj lam
      = do let base = if null tag then "let" else tag
           r  <- initRefV base =<< goAST a
           a' <- unsafeFreezeRefV r
           localAlias v a' $ goAST body
    go t tup (a :* b :* Syn.Nil)
      | Just Pair <- prj tup
      = Branch <$> goAST a <*> goAST b
    go t sel (ab :* Syn.Nil)
      | Just Fst <- prj sel = do
          Branch a _ <- goAST ab
          return a
      | Just Snd <- prj sel = do
          Branch _ b <- goAST ab
          return b
    go ty cond (b :* t :* f :* Syn.Nil)
      | Just Cond <- prj cond = do
          res <- newRefV ty "b"
          b'  <- goSmallAST b
          ReaderT $ \env -> iff b'
            (flip runReaderT env $ setRefV res =<< goAST t)
            (flip runReaderT env $ setRefV res =<< goAST f)
          unsafeFreezeRefV res
    go _ op (a :* Syn.Nil)
      | Just Neg <- prj op = liftStruct (sugarSymPrim Neg) <$> goAST a
      | Just Not <- prj op = liftStruct (sugarSymPrim Not) <$> goAST a
      | Just Sin <- prj op = liftStruct (sugarSymPrim Sin) <$> goAST a
      | Just Cos <- prj op = liftStruct (sugarSymPrim Cos) <$> goAST a
      | Just Tan <- prj op = liftStruct (sugarSymPrim Tan) <$> goAST a
      | Just I2N <- prj op = liftStruct (sugarSymPrim I2N) <$> goAST a
      | Just BitCompl <- prj op = liftStruct (sugarSymPrim BitCompl) <$> goAST a
    go _ op (a :* b :* Syn.Nil)
      | Just Add <- prj op = liftStruct2 (sugarSymPrim Add) <$> goAST a <*> goAST b
      | Just Sub <- prj op = liftStruct2 (sugarSymPrim Sub) <$> goAST a <*> goAST b
      | Just Mul <- prj op = liftStruct2 (sugarSymPrim Mul) <$> goAST a <*> goAST b
      | Just Div <- prj op = liftStruct2 (sugarSymPrim Div) <$> goAST a <*> goAST b
      | Just Mod <- prj op = liftStruct2 (sugarSymPrim Mod) <$> goAST a <*> goAST b
      | Just Eq  <- prj op = liftStruct2 (sugarSymPrim Eq)  <$> goAST a <*> goAST b
      | Just And <- prj op = liftStruct2 (sugarSymPrim And) <$> goAST a <*> goAST b
      | Just Or  <- prj op = liftStruct2 (sugarSymPrim Or)  <$> goAST a <*> goAST b
      | Just Lt  <- prj op = liftStruct2 (sugarSymPrim Lt)  <$> goAST a <*> goAST b
      | Just Lte <- prj op = liftStruct2 (sugarSymPrim Lte) <$> goAST a <*> goAST b
      | Just Gt  <- prj op = liftStruct2 (sugarSymPrim Gt)  <$> goAST a <*> goAST b
      | Just Gte <- prj op = liftStruct2 (sugarSymPrim Gte) <$> goAST a <*> goAST b
      | Just BitAnd <- prj op =
          liftStruct2 (sugarSymPrim BitAnd)  <$> goAST a <*> goAST b
      | Just BitOr  <- prj op =
          liftStruct2 (sugarSymPrim BitOr)   <$> goAST a <*> goAST b
      | Just BitXor <- prj op =
          liftStruct2 (sugarSymPrim BitXor)  <$> goAST a <*> goAST b
      | Just ShiftL <- prj op =
          liftStruct2 (sugarSymPrim ShiftL)  <$> goAST a <*> goAST b
      | Just ShiftR <- prj op =
          liftStruct2 (sugarSymPrim ShiftR)  <$> goAST a <*> goAST b
      | Just RotateL <- prj op =
          liftStruct2 (sugarSymPrim RotateL) <$> goAST a <*> goAST b
      | Just RotateR <- prj op =
          liftStruct2 (sugarSymPrim RotateR) <$> goAST a <*> goAST b
    go t loop (len :* init :* (lami :$ (lams :$ body)) :* Syn.Nil)
      | Just ForLoop   <- prj loop
      , Just (LamT iv) <- prj lami
      , Just (LamT sv) <- prj lams
      , trace ("names: (" ++ show iv ++ ", " ++ show sv ++ ")") True = do
          len'  <- goSmallAST len
          state <- initRefV "state" =<< goAST init
          ReaderT $ \env -> Imp.for (0, 1, Imp.Excl len') $ \i ->
            flip runReaderT env $ do
              s <- case t of
                Node _ -> unsafeFreezeRefV state
                _      -> getRefV state
              s' <- localAlias iv (Node i) $ localAlias sv s $ goAST body
              setRefV state s'
          unsafeFreezeRefV state
    go _ arrIx (i :* Syn.Nil)
      | Just (ArrIx arr) <- prj arrIx = do
          i' <- goSmallAST i
          return $ Node $ sugarSymPrim (ArrIx arr) i'
    go _ s _ = error $ "software translation handling for symbol " ++ Syn.renderSym s ++ " is missing."

unsafeTranslateSmallExp :: Monad m => SExp a -> TargetT m (Prim a)
unsafeTranslateSmallExp a = do
  Node b <- translateExp a
  return b

--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

translateCMD ::
     ProgramT SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) m a
  -> ProgramT TargetCMD   (Oper.Param2 SExp SoftwarePrimType) m a
translateCMD = undefined

--------------------------------------------------------------------------------

translate :: Software a -> ProgC a
translate = flip runReaderT Map.empty
          . Oper.reexpressEnv unsafeTranslateSmallExp
            -- todo: 
          . translateCMD
            --
          . unSoftware

--------------------------------------------------------------------------------
-- * Interpretation of software programs.
--------------------------------------------------------------------------------

runIO :: Software a -> IO a
runIO = Imp.runIO . translate

captureIO :: Software a -> String -> IO String
captureIO = Imp.captureIO . translate

compile :: Software a -> String
compile = Imp.compile . translate

icompile :: Software a -> IO ()
icompile = Imp.icompile . translate

runCompiled :: Software a -> IO ()
runCompiled = Imp.runCompiled . translate

withCompiled :: Software a -> ((String -> IO String) -> IO b) -> IO b
withCompiled = Imp.withCompiled . translate

compareCompiled :: Software a -> IO a -> String -> IO ()
compareCompiled = Imp.compareCompiled . translate

--------------------------------------------------------------------------------
