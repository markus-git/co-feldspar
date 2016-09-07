{-# language GADTs #-}
{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

module Feldspar.Software.Primitive.Backend where

import Feldspar.Software.Primitive

import Data.Constraint (Dict (..))
import Data.Proxy

-- syntactic.
import Language.Syntactic

-- language-c-quote.
import Language.C.Quote.C
import qualified Language.C.Syntax as C

--imperative-edsl.
import Language.C.Monad
import Language.Embedded.Backend.C

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

viewLitPrim :: ASTF SoftwarePrimitiveDomain a -> Maybe a
viewLitPrim (Sym (Lit a :&: _)) = Just a
viewLitPrim _                   = Nothing

--------------------------------------------------------------------------------

instance CompTypeClass SoftwarePrimType
  where
    compType _ (_ :: proxy a) = case softwareRep :: SoftwareTypeRep a of
      BoolST  -> addInclude "<stdbool.h>" >> return [cty| typename bool |]
      Int8ST  -> addInclude "<stdint.h>"  >> return [cty| typename int8_t |]
      Word8ST -> addInclude "<stdint.h>"  >> return [cty| typename uint8_t |]
      FloatST -> return [cty| float |]

    compLit _ a = case sPrimTypeOf a of
      BoolST  ->
        do addInclude "<stdbool.h>"
           return $ if a then [cexp| true |] else [cexp| false |]
      Int8ST  -> return [cexp| $a |]
      Word8ST -> return [cexp| $a |]
      FloatST -> return [cexp| $a |]

--------------------------------------------------------------------------------

instance CompExp Prim
  where
    compExp = compPrim

--------------------------------------------------------------------------------

compUnOp
  :: MonadC m
  => C.UnOp
  -> ASTF SoftwarePrimitiveDomain a
  -> m C.Exp
compUnOp op a = do
  a' <- compPrim $ Prim a
  return $ C.UnOp op a' mempty

compBinOp
  :: MonadC m
  => C.BinOp
  -> ASTF SoftwarePrimitiveDomain a
  -> ASTF SoftwarePrimitiveDomain b
  -> m C.Exp
compBinOp op a b = do
  a' <- compPrim $ Prim a
  b' <- compPrim $ Prim b
  return $ C.BinOp op a' b' mempty  

compFun
  :: MonadC m
  => String
  -> Args (AST SoftwarePrimitiveDomain) sig
  -> m C.Exp
compFun fun args = do
  as <- sequence $ listArgs (compPrim . Prim) args
  return [cexp| $id:fun($args:as) |]

--------------------------------------------------------------------------------

compPrim :: MonadC m => Prim a -> m C.Exp
compPrim = simpleMatch (\(s :&: t) -> go t s) . unPrim
  where
    go :: forall m sig
       .  MonadC m
       => SoftwareTypeRep (DenResult sig)
       -> SoftwarePrimitiveConstructs sig
       -> Args (AST SoftwarePrimitiveDomain) sig
       -> m C.Exp
    go _ (FreeVar v) Nil = touchVar v >> return [cexp| $id:v |]
    go t (Lit a)     Nil | Dict <- sPrimWitType t = compLit (Proxy :: Proxy SoftwarePrimType) a
    go _ Neg (a :* Nil)      = compUnOp  C.Negate a
    go _ Add (a :* b :* Nil) = compBinOp C.Add a b
    go _ Sub (a :* b :* Nil) = compBinOp C.Sub a b
    go _ Mul (a :* b :* Nil) = compBinOp C.Mul a b
    go _ Div (a :* b :* Nil) = compBinOp C.Div a b
    go _ Mod (a :* b :* Nil) = compBinOp C.Mod a b
    go _ Not (a :* Nil)      = compUnOp  C.Lnot a
    go _ And (a :* b :* Nil) = compBinOp C.Land a b
    go _ Eq  (a :* b :* Nil) = compBinOp C.Eq a b
    go _ Lt  (a :* b :* Nil) = compBinOp C.Lt a b
    go _ Sin args = addInclude "<tgmath.h>" >> compFun "sin" args
    go _ Cos args = addInclude "<tgmath.h>" >> compFun "cos" args
    go _ Tan args = addInclude "<tgmath.h>" >> compFun "tan" args

--------------------------------------------------------------------------------
