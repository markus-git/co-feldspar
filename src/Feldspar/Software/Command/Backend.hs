{-# LANGUAGE QuasiQuotes #-}

module Feldspar.Software.Command.Backend where

-- language-c-quot
import Language.C.Quote.GCC
import qualified Language.C.Syntax as C

--------------------------------------------------------------------------------
-- * Translation of software commands into C.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** ...
{-
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
-}

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
