{-# language GADTs               #-}
{-# language TypeOperators       #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}
{-# language ConstraintKinds #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language QuasiQuotes #-}

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

import Data.Selection
import Data.Default.Class

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
--import Language.Embedded.Imperative hiding (Ref, (:+:)(..), (:<:)(..))
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp
import qualified Language.Embedded.Imperative.Frontend as Imp
import qualified Language.Embedded.Backend.C  as Imp
import qualified Language.C.Monad as C
  (CGen, addGlobal, addLocal, addInclude, addStm, gensym)

-- hardware-edsl
import qualified Language.Embedded.Hardware.Command as Hard

-- language-c-quote
import Language.C.Quote.GCC
import qualified Language.C.Syntax as C

-- hmm!
import Feldspar.Hardware.Primitive  (HardwarePrimType(..), HardwarePrimTypeRep(..))
import Feldspar.Hardware.Expression (HType')
import Feldspar.Hardware.Frontend   (HSig, withHType')

-- debug.
import Debug.Trace

--------------------------------------------------------------------------------
-- * Software compiler.
--------------------------------------------------------------------------------

-- | Target software instructions.
type TargetCMD
    =        Imp.RefCMD
    Oper.:+: Imp.ArrCMD
    Oper.:+: Imp.ControlCMD
    Oper.:+: Imp.FileCMD
    Oper.:+: Imp.PtrCMD
    Oper.:+: Imp.C_CMD
    --
    Oper.:+: PtrCMD
    Oper.:+: MMapCMD

-- | Target monad during translation.
type TargetT m = ReaderT Env (Oper.ProgramT TargetCMD (Oper.Param2 Prim SoftwarePrimType) m)

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
unsafeFreezeRefV = lift . mapStructA Imp.unsafeFreezeRef

--------------------------------------------------------------------------------
-- ** Compilation options.

-- | Options affecting code generation
--
-- A default set of options is given by 'def'.
--
-- The assertion labels to include in the generated code can be stated using the
-- functions 'select', 'allExcept' and 'selectBy'. For example
--
-- @`def` {compilerAssertions = `allExcept` [`InternalAssertion`]}@
--
-- states that we want to include all except internal assertions.
data CompilerOpts = CompilerOpts
    { compilerAssertions :: Selection AssertionLabel
        -- ^ Which assertions to include in the generated code
    }

instance Default CompilerOpts
  where
    def = CompilerOpts
      { compilerAssertions = universal
      }

--------------------------------------------------------------------------------
-- ** Compilation environment.

data Env = Env {
    envAliases :: Map Name VExp'
  , envOptions :: CompilerOpts
  }

env0 :: Env
env0 = Env Map.empty def

localAlias :: MonadReader Env m => Name -> VExp a -> m b -> m b
localAlias v e = local (\env ->
  env {envAliases = Map.insert v (VExp' e) (envAliases env)})

lookAlias :: MonadReader Env m => STypeRep a -> Name -> m (VExp a)
lookAlias t v = do
  env <- asks envAliases
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
          branch <- goAST ab
          case branch of (Branch a _) -> return a
      | Just Snd <- prj sel = do
          branch <- goAST ab
          case branch of (Branch _ b) -> return b
    go ty cond (b :* t :* f :* Syn.Nil)
      | Just Cond <- prj cond = do
          res <- newRefV ty "b"
          b'  <- goSmallAST b
          ReaderT $ \env -> Imp.iff b'
            (flip runReaderT env $ setRefV res =<< goAST t)
            (flip runReaderT env $ setRefV res =<< goAST f)
          unsafeFreezeRefV res
    go _ op (a :* Syn.Nil)
      | Just Neg       <- prj op = liftStruct (sugarSymPrim Neg)       <$> goAST a
      | Just Not       <- prj op = liftStruct (sugarSymPrim Not)       <$> goAST a
      | Just Exp       <- prj op = liftStruct (sugarSymPrim Exp)       <$> goAST a
      | Just Log       <- prj op = liftStruct (sugarSymPrim Log)       <$> goAST a
      | Just Sqrt      <- prj op = liftStruct (sugarSymPrim Sqrt)      <$> goAST a
      | Just Sin       <- prj op = liftStruct (sugarSymPrim Sin)       <$> goAST a
      | Just Cos       <- prj op = liftStruct (sugarSymPrim Cos)       <$> goAST a
      | Just Tan       <- prj op = liftStruct (sugarSymPrim Tan)       <$> goAST a
      | Just Asin      <- prj op = liftStruct (sugarSymPrim Asin)      <$> goAST a
      | Just Acos      <- prj op = liftStruct (sugarSymPrim Acos)      <$> goAST a
      | Just Atan      <- prj op = liftStruct (sugarSymPrim Atan)      <$> goAST a
      | Just Sinh      <- prj op = liftStruct (sugarSymPrim Sinh)      <$> goAST a
      | Just Cosh      <- prj op = liftStruct (sugarSymPrim Cosh)      <$> goAST a
      | Just Tanh      <- prj op = liftStruct (sugarSymPrim Tanh)      <$> goAST a
      | Just Asinh     <- prj op = liftStruct (sugarSymPrim Asinh)     <$> goAST a
      | Just Acosh     <- prj op = liftStruct (sugarSymPrim Acosh)     <$> goAST a
      | Just Atanh     <- prj op = liftStruct (sugarSymPrim Atanh)     <$> goAST a
      | Just Real      <- prj op = liftStruct (sugarSymPrim Real)      <$> goAST a
      | Just Imag      <- prj op = liftStruct (sugarSymPrim Imag)      <$> goAST a
      | Just Magnitude <- prj op = liftStruct (sugarSymPrim Magnitude) <$> goAST a
      | Just Phase     <- prj op = liftStruct (sugarSymPrim Phase)     <$> goAST a
      | Just Conjugate <- prj op = liftStruct (sugarSymPrim Conjugate) <$> goAST a
      | Just I2N       <- prj op = liftStruct (sugarSymPrim I2N)       <$> goAST a
      | Just I2B       <- prj op = liftStruct (sugarSymPrim I2B)       <$> goAST a
      | Just B2I       <- prj op = liftStruct (sugarSymPrim B2I)       <$> goAST a
      | Just Round     <- prj op = liftStruct (sugarSymPrim Round)     <$> goAST a
      | Just BitCompl  <- prj op = liftStruct (sugarSymPrim BitCompl)  <$> goAST a
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
      | Just FDiv    <- prj op =
          liftStruct2 (sugarSymPrim FDiv)    <$> goAST a <*> goAST b
      | Just Complex <- prj op =
          liftStruct2 (sugarSymPrim Complex) <$> goAST a <*> goAST b
      | Just Polar   <- prj op =
          liftStruct2 (sugarSymPrim Polar)   <$> goAST a <*> goAST b
      | Just Pow     <- prj op =
          liftStruct2 (sugarSymPrim Pow)     <$> goAST a <*> goAST b
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
    go t guard (cond :* a :* Syn.Nil)
      | Just (GuardVal lbl msg) <- prj guard
      = do cond' <- extractNode <$> goAST cond
           lift $ Imp.assert cond' msg
           goAST a
    go t hint (cond :* a :* Syn.Nil)
        | Just (HintVal) <- prj hint
        = do cond' <- extractNode <$> goAST cond
             lift $ Imp.hint cond'
             goAST a
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
  node <- translateExp a
  case node of (Node b) -> return b

--------------------------------------------------------------------------------
-- * Interpretation of software commands.
--------------------------------------------------------------------------------

instance (Imp.CompExp exp, Imp.CompTypeClass ct) =>
    Oper.Interp PtrCMD C.CGen (Oper.Param2 exp ct)
  where
    interp = compPtrCMD

compPtrCMD :: forall exp ct a . (Imp.CompExp exp, Imp.CompTypeClass ct) =>
  PtrCMD (Oper.Param3 C.CGen exp ct) a -> C.CGen a
compPtrCMD = undefined

--------------------------------------------------------------------------------

instance (Imp.CompExp exp, Imp.CompTypeClass ct) =>
    Oper.Interp MMapCMD C.CGen (Oper.Param2 exp ct)
  where
    interp = compMMapCMD

-- todo:
--  > only need one 'ix' for read/write to arrays in 'Call'.
--  > 'n' in 'MMap' isn't really an '$id'.
compMMapCMD :: forall exp ct a . (Imp.CompExp exp, Imp.CompTypeClass ct) =>
  MMapCMD (Oper.Param3 C.CGen exp ct) a -> C.CGen a
compMMapCMD (MMap n sig) =
  do C.addInclude "<stdio.h>"
     C.addInclude "<stdlib.h>"
     C.addInclude "<stddef.h>"
     C.addInclude "<unistd.h>"
     C.addInclude "<sys/mman.h>"
     C.addInclude "<fcntl.h>"
     C.addGlobal [cedecl| unsigned page_size = 0; |]
     C.addGlobal [cedecl| int mem_fd = -1; |]
     C.addGlobal mmap_def
     mem <- C.gensym "mem"
     C.addLocal [cdecl| int * $id:mem = f_map($id:n); |]
     return mem
compMMapCMD (Call (Address ptr sig) arg) =
  do traverse 0 sig arg
  where
    traverse :: Integer -> HSig b -> Argument ct (Soften b) -> C.CGen ()
    traverse ix (Hard.Ret _) (Nil) = return ()
    traverse ix (Hard.SSig _ Hard.Out rf) (ARef (Ref (Node ref@(Imp.RefComp r))) arg) =
      do typ <- compRefType (Proxy :: Proxy ct) ref
         C.addStm [cstm| $id:r = ($ty:typ) *($id:ptr + $int:ix); |]
         traverse (ix + 1) (rf dummy) arg
    traverse ix (Hard.SArr _ Hard.Out len af) (AArr (Arr _ _ (Node arr@(Imp.ArrComp a))) arg) =
      do let end = ix + toInteger len
         i   <- C.gensym "ix"
         typ <- compArrType (Proxy :: Proxy ct) arr
         C.addLocal [cdecl| int $id:i; |]
         C.addStm [cstm| for ($id:i=$int:ix; $id:i<$int:end; $id:i++) {
                           $id:arr[$id:i] = ($ty:typ) *($id:ptr + $id:i);
                         } |]
         traverse end (af dummy) arg
    traverse ix (Hard.SSig _ Hard.In rf) (ARef (Ref (Node (Imp.RefComp r))) arg) =
      do C.addStm [cstm| *($id:ptr + $int:ix) = (int) $id:r; |]
         traverse (ix + 1) (rf dummy) arg
    traverse ix (Hard.SArr _ Hard.In len af) (AArr (Arr _ _ (Node arr@(Imp.ArrComp a))) arg) =
      do let end = ix + toInteger len
         i   <- C.gensym "ix"
         typ <- compArrType (Proxy :: Proxy ct) arr
         C.addLocal [cdecl| int $id:i; |]
         C.addStm [cstm| for ($id:i=$int:ix; $id:i<$int:end; $id:i++) {
                           *($id:ptr + $id:i) = (int) $id:arr[$id:i];
                         } |]
         traverse end (af dummy) arg

    dummy :: forall x . x
    dummy = error "dummy evaluated."

    compRefType :: forall x . (Imp.CompTypeClass ct, HardwarePrimType x, ct x)
      => Proxy ct -> Imp.Ref x -> C.CGen C.Type
    compRefType ct _ = case witnessSP (Proxy :: Proxy x) of
      Dict -> Imp.compType ct (Proxy :: Proxy x)

    compArrType :: forall i x . (Imp.CompTypeClass ct, HardwarePrimType x, ct x)
      => Proxy ct -> Imp.Arr i x -> C.CGen C.Type
    compArrType ct _ = case witnessSP (Proxy :: Proxy x) of
      Dict -> Imp.compType ct (Proxy :: Proxy x)

    witnessSP :: forall x . HardwarePrimType x => Proxy x -> Dict (SoftwarePrimType x)
    witnessSP _ = case hardwareRep :: HardwarePrimTypeRep x of
      BoolHT    -> Dict
      Int8HT    -> Dict
      Int16HT   -> Dict
      Int32HT   -> Dict
      Int64HT   -> Dict
      Word8HT   -> Dict
      Word16HT  -> Dict
      Word32HT  -> Dict
      Word64HT  -> Dict
      _         -> error "unrecognized software type used by mmap."

--------------------------------------------------------------------------------

mmap_def :: C.Definition
mmap_def = [cedecl|
int * f_map(unsigned addr) {
  unsigned page_addr;
  unsigned offset;
  void * ptr;
  if (!page_size) {
    page_size = sysconf(_SC_PAGESIZE);
  }
  if (mem_fd < 1) {
    mem_fd = open("/dev/mem", O_RDWR);
    if (mem_fd < 1) {
      perror("f_map");
    }
  }
  page_addr = (addr & (~(page_size - 1)));
  offset = addr - page_addr;
  ptr = mmap(NULL, page_size, PROT_READ|PROT_WRITE, MAP_SHARED, mem_fd, page_addr);
  if (ptr == MAP_FAILED || !ptr) {
    perror("f_map");
  }
  return (int*) (ptr + offset);
}
|]

--------------------------------------------------------------------------------

translate' :: Env -> Software a -> ProgC a
translate' env =
    flip runReaderT env
  . Oper.reexpressEnv unsafeTranslateSmallExp
  . unSoftware
  
translate :: Software a -> ProgC a
translate = translate' env0

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
runCompiled = Imp.runCompiled' opts . translate

withCompiled :: Software a -> ((String -> IO String) -> IO b) -> IO b
withCompiled = Imp.withCompiled' opts . translate

compareCompiled :: Software a -> IO a -> String -> IO ()
compareCompiled = Imp.compareCompiled' opts . translate

opts :: Imp.ExternalCompilerOpts
opts = Imp.def { Imp.externalFlagsPost = ["-lm"] }

--------------------------------------------------------------------------------

runCompiled' ::
       CompilerOpts
    -> Imp.ExternalCompilerOpts
    -> Software a
    -> IO ()
runCompiled' opts eopts = Imp.runCompiled' eopts . translate' (Env mempty opts)

--------------------------------------------------------------------------------
