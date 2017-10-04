module Feldspar.Software.Command where

import Feldspar.Software.Expression

-- operational-higher.
import Control.Monad.Operational.Higher

-- imperative-edsl.
-- ...

--------------------------------------------------------------------------------
-- * Software commands.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Memory mapping.
{-
-- todo : must it really be closed?
type family Soften a where
  Soften () = ()
  Soften (H.Signal a -> b) = Imp.Ref a       -> Soften b
  Soften (H.Array  a -> b) = Imp.Arr Index a -> Soften b

-- todo : these two families could probably be better.
type family Result a where
  Result ()                    = ()
  Result (Imp.Ref a -> ())       = Ref (SExp a)
  Result (Imp.Ref a -> b)        = Result b
  Result (Imp.Arr Index a -> ()) = Arr (SExp a)
  Result (Imp.Arr Index a -> b)  = Result b

-- todo : yep, most likely.
type family Argument a where
  Argument ()        = ()
  Argument (a -> ()) = ()
  Argument (a -> b)  = a -> Argument b

data MMapCMD fs a
  where
    MMap :: String -> Sig a
         -> MMapCMD (Param3 prog exp pred) (Address (Soften a))
    Call :: Address a -> SArg (Argument a)
         -> MMapCMD (Param3 prog exp pred) (Result a)

-- todo : I ignore translations for the signature. I think this is correct,
--        since the software side should not touch the hardware program inside,
--        but I should double check this later. This todo goes for all
--        instance declarations below.
instance Oper.HFunctor MMapCMD
  where
    hfmap _ (MMap n sig)     = MMap n sig
    hfmap _ (Call addr args) = Call addr args

instance Oper.HBifunctor MMapCMD
  where
    hbimap _ _ (MMap n sig)     = MMap n sig
    hbimap _ _ (Call addr args) = Call addr args

instance (MMapCMD Imp.:<: instr) => Oper.Reexpressible MMapCMD instr env
  where
    reexpressInstrEnv reexp (MMap n sig) = ReaderT $ \env ->
      Oper.singleInj $ MMap n sig
    reexpressInstrEnv reexp (Call addr args) = ReaderT $ \env ->
      Oper.singleInj $ Call addr args
-}
--------------------------------------------------------------------------------
