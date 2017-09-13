{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language ConstraintKinds #-}
{-# language ScopedTypeVariables #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}

module Feldspar.Software.Compile where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Common

import Feldspar.Software.Primitive
import Feldspar.Software.Primitive.Backend
import Feldspar.Software.Expression
import Feldspar.Software.Representation
-- todo : hmm...
import Feldspar.Software.Frontend

import Feldspar.Hardware.Representation (Sig)

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
import Language.Embedded.Concurrent
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp
import qualified Language.Embedded.Backend.C      as Imp
import qualified Language.C.Monad as C

-- language-c-quot
import Language.C.Quote.GCC
import qualified Language.C.Syntax as C

-- hardware-edsl
import qualified Language.Embedded.Hardware.Command.CMD as Imp

--------------------------------------------------------------------------------
-- * Software compiler.
--------------------------------------------------------------------------------

compile :: Software a -> String
compile = Imp.compile . translate

icompile :: Software a -> IO ()
icompile = Imp.icompile . translate

--------------------------------------------------------------------------------
-- ** Instructions.
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
    -- ...
    Oper.:+: MMapCMD

-- | Target monad during translation
type TargetT m = ReaderT Env (ProgramT TargetCMD (Oper.Param2 Prim SoftwarePrimType) m)

-- | Monad for translated program
type ProgC = Program TargetCMD (Oper.Param2 Prim SoftwarePrimType)

--------------------------------------------------------------------------------

instance (Imp.CompExp exp, Imp.CompTypeClass ct)
  => Oper.Interp MMapCMD C.CGen (Param2 exp ct)
  where
    interp = compMMapCMD

compMMapCMD
  :: forall exp ct a
   . (Imp.CompExp exp, Imp.CompTypeClass ct)
  => MMapCMD (Param3 C.CGen exp ct) a
  -> C.CGen a
compMMapCMD cmd@(MMap n sig) =
  do C.addInclude "<stdio.h>"
     C.addInclude "<stdlib.h>"
     C.addInclude "<stddef.h>"
     C.addInclude "<unistd.h>"
     C.addInclude "<sys/mman.h>"
     C.addInclude "<fcntl.h>"
     C.addGlobal [cedecl| unsigned page_size = 0; |]
     C.addGlobal [cedecl| int mem_fd = -1; |]
     C.addGlobal mmapDef
     mem <- C.gensym "mem"
     C.addLocal [cdecl| int * $id:mem = f_map($string:n); |]
     soften mem 0 sig
  where
    soften :: String -> Int -> Sig b -> C.CGen (Address (Soften b))
    soften _ _ (SigRet _)       = return AddrRet
    soften m i (SigSignal n _ sf) = do
      ref <- Imp.RefComp <$> C.gensym "proc"
      C.addLocal [cdecl| int $id:ref = *($id:m + $int:i); |]
      adr <- soften m (i+1) (sf dummy)
      return $ AddrRef ref (const adr)
    soften m i (SigArray n _ len af) = do
      ref <- Imp.RefComp <$> C.gensym "proc"
      C.addLocal [cdecl| int $id:ref = *($id:m + $int:i); |]
      adr <- soften m (i+1) (af dummy)
      return $ AddrArr ref len (const adr)
    -- todo : I should remove this one.
    dummy :: b
    dummy = error "co-feldspar.soften: evaluated signature."
    -- todo : get types of 'channel -> ref/arr'.
    proxySig :: (c b -> Signature fs d) -> Proxy b
    proxySig _ = (Proxy::Proxy b)

compMMapCMD cmd@(Call addr args) =
  do res <- apply addr args
     return $ result res addr
  where
    result :: forall b . String -> Address b -> Result b
    result s (AddrRet) = ()
    result s (AddrRef _ (rf :: Imp.Ref c -> Address d)) =
      case rf dummy of
        a@(AddrRet)       -> Ref (Node (Imp.RefComp s)) :: Result b
        a@(AddrRef _ _)   -> result s a
        a@(AddrArr _ _ _) -> result s a
    result s (AddrArr _ l (af :: Imp.Arr Index c -> Address d)) =
      case af dummy of
        a@(AddrRet)       -> Arr 0 (fromIntegral l) (Node (Imp.ArrComp s))
        a@(AddrRef _ _)   -> result s a
        a@(AddrArr _ _ _) -> result s a
    -- todo : return a new reference instead of the channel one, so users
    --        cannot do wierd things with it.
    --
    -- todo : the type I use is temporary, this function shuold have the following
    --        type instead:
    --
    -- apply :: Address b -> SArg (Argument b) -> C.CGen (Result b)
    --
    -- todo : avoid the extra compilation steps here by instead invocing the
    --        compiler from the respective languages. That is, create a instruction
    --        like below and call 'Oper.interp'. This requires 'Adddress' to have
    --        its predicate be a parameter (like instructions with 'fs' do).
    --
    -- let ri :: Imp.RefCMD (Imp.Param3 C.CGen exp ct) (Imp.Ref x)
    --     ri  = Imp.NewRef "res"
    --
    apply :: Address b -> SArg c -> C.CGen String
    apply (AddrRef
             (ref :: (Imp.Ref Int32))
             (rf  :: (Imp.Ref x -> Address y)))
          (SoftNil) =
      do out <- C.gensym "res"
         C.addLocal [cdecl| int $id:out; |]
         C.addStm [cstm| $id:out = $id:ref; |]
         return out
    apply (AddrRef ref rf) (SoftRef arg as) =
      do C.addStm [cstm| $id:ref = (int) $id:arg; |]
         apply (rf dummy) as
    apply (AddrArr ref len af) (SoftNil) =
      do sym <- C.gensym "res"
         let sym' = '_':sym
         count <- Imp.RefComp <$> C.gensym "v"
         C.addLocal [cdecl| int $id:count; |]
         C.addLocal [cdecl| int $id:sym'[ $int:len ]; |]
         C.addLocal [cdecl| int * $id:sym = $id:sym'; |]
         C.addStm   [cstm|
             for($id:count=0;$id:count<$int:len;$id:count++) {
               $id:sym[$id:count] = $id:ref;
             } |]
         return sym
    apply (AddrArr ref len af) (SoftArr arg as) =
      do count <- Imp.RefComp <$> C.gensym "v"
         C.addLocal [cdecl| int $id:count; |]
         C.addStm   [cstm|
             for($id:count=0;$id:count<$int:len;$id:count++) {
               $id:ref = (int) $id:arg[$id:count];
             } |]
         apply (af dummy) as
    -- todo : ...
    proxyAddr :: (c b -> Address d) -> Proxy b
    proxyAddr _ = Proxy::Proxy b
    -- todo : I should remove this one.
    dummy :: b
    dummy = error "co-feldspar.apply: evaluated signature."

mmapDef :: C.Definition
mmapDef =  [cedecl|
int * f_map(unsigned addr) {
  unsigned page_addr;
  unsigned offset;
  void * ptr;
  if(!page_size) {
    page_size = sysconf(_SC_PAGESIZE);
  }
  if(mem_fd < 1) {
    mem_fd = open ("/dev/mem", O_RDWR);
    if (mem_fd < 1) {
      perror("f_map");
    }
  }
  page_addr = (addr & (~(page_size-1)));
  offset = addr - page_addr;
  ptr = mmap(NULL, page_size, PROT_READ|PROT_WRITE, MAP_SHARED, mem_fd, page_addr);
  if(ptr == MAP_FAILED || !ptr) {
    perror("f_map");
  }
  return (int*) (ptr + offset);
}
|]

--------------------------------------------------------------------------------
-- ** Expressions.
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

translateExp :: forall m a . Monad m => SExp a -> TargetT m (VExp a)
translateExp = goAST . unSExp
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
      = lookAlias t v
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
    go t loop (len :* init :* (lami :$ (lams :$ body)) :* Syn.Nil)
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

translate :: Software a -> ProgC a
translate = flip runReaderT Map.empty . Oper.reexpressEnv unsafeTranslateSmallExp . unSoftware

--------------------------------------------------------------------------------
