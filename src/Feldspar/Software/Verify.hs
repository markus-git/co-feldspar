{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeOperators #-}
{-# language PolyKinds #-}
{-# language FlexibleContexts #-}

module Feldspar.Software.Verify where

import Feldspar.Software.Representation (Software(..), SoftwareCMD, AssertCMD, ControlCMD(..), PtrCMD, MMapCMD)
import Feldspar.Software.Primitive (Prim, SoftwarePrimType)
import Feldspar.Software.Compile (ProgC, translate)
import Feldspar.Software.Verify.Command
import Feldspar.Software.Verify.Primitive

import qualified Feldspar.Verify.Monad as V
import qualified Feldspar.Verify.FirstOrder as FO

-- imperative-edsl.
import qualified Language.Embedded.Imperative.CMD as Imp
import qualified Language.Embedded.Backend.C as Imp

-- operational-higher.
import Control.Monad.Operational.Higher

--------------------------------------------------------------------------------
-- * Verification of Software programs.
--------------------------------------------------------------------------------

verifySoft :: Software () -> IO ()
verifySoft = verifiedSoft Imp.icompile

verifiedSoft :: (ProgC () -> IO a) -> Software () -> IO a
verifiedSoft comp prog =
  do (prg, ws) <- V.runVerify $ do
       return $ declareFeldsparGlobals
       V.verify $ translate $ prog
     comp prg <* unless (null ws) (do
       putStrLn "Warnings:"
       sequence_ [ putStrLn ('\t' : warn) | warn <- ws])

--------------------------------------------------------------------------------

instance V.Verifiable
    (Program
      (    Imp.RefCMD
       :+: Imp.ArrCMD
       :+: Imp.ControlCMD
       :+: Imp.FileCMD
       :+: Imp.PtrCMD
       :+: Imp.C_CMD
       :+: PtrCMD
       :+: MMapCMD
      )
      (Param2 Prim SoftwarePrimType))
  where
    verifyWithResult prog = do
      let inv = undefined :: [[SomeLiteral]]
      (p, r) <- V.verifyWithResult (FO.defunctionalise inv prog)
      return (FO.refunctionalise inv p, r)

instance V.Verifiable
    (FO.Sequence
      (    Imp.RefCMD
       :+: Imp.ArrCMD
       :+: ControlCMD [[SomeLiteral]]
       :+: Imp.FileCMD
       :+: Imp.PtrCMD
       :+: Imp.C_CMD
       :+: PtrCMD
       :+: MMapCMD
      )
      (Param2 Prim SoftwarePrimType))
  where
    verifyWithResult (FO.Val a)     = return (FO.Val a, a)
    verifyWithResult (FO.Seq a m k) = do
      ((m', breaks), warns) <- V.swallowWarns $ 
        V.getWarns $ V.withBreaks $ V.verifyInstr m a
      (_, (k', res)) <-
        V.ite breaks (return ()) (V.verifyWithResult k)
      let
        comment msg prog = flip (FO.Seq ()) prog (inj
          (Comment msg :: ControlCMD [[SomeLiteral]] (Param3
            (FO.Sequence prog (Param2 Prim SoftwarePrimType))
            (Prim) (SoftwarePrimType)) ()))
      return (foldr comment (FO.Seq a m' k') warns, res)

--------------------------------------------------------------------------------

instance FO.Defunctionalise inv AssertCMD where refunc = error "todo: assert"
instance FO.Defunctionalise inv PtrCMD    where refunc = error "todo: ptr"
instance FO.Defunctionalise inv MMapCMD   where refunc = error "todo: mmap"

instance V.VerifyInstr AssertCMD exp pred where verifyInstr = error "todo: assert"
instance V.VerifyInstr PtrCMD    exp pred where verifyInstr = error "todo: ptr"
instance V.VerifyInstr MMapCMD   exp pred where verifyInstr = error "todo: mmap"

--------------------------------------------------------------------------------
