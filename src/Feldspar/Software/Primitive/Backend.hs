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
-- * Compilation of software primitives.
--------------------------------------------------------------------------------

viewLitPrim :: ASTF SoftwarePrimDomain a -> Maybe a
viewLitPrim (Sym (Lit a :&: _)) = Just a
viewLitPrim _                   = Nothing

--------------------------------------------------------------------------------

instance CompTypeClass SoftwarePrimType
  where
    compType _ (_ :: proxy a) = case softwareRep :: SoftwarePrimTypeRep a of
      BoolST   -> addInclude "<stdbool.h>" >> return [cty| typename bool |]
      Int8ST   -> addInclude "<stdint.h>"  >> return [cty| typename int8_t |]
      Int16ST  -> addInclude "<stdint.h>"  >> return [cty| typename int16_t |]
      Int32ST  -> addInclude "<stdint.h>"  >> return [cty| typename int32_t |]
      Int64ST  -> addInclude "<stdint.h>"  >> return [cty| typename int64_t |]
      Word8ST  -> addInclude "<stdint.h>"  >> return [cty| typename uint8_t |]
      Word16ST -> addInclude "<stdint.h>"  >> return [cty| typename uint16_t |]
      Word32ST -> addInclude "<stdint.h>"  >> return [cty| typename uint32_t |]
      Word64ST -> addInclude "<stdint.h>"  >> return [cty| typename uint64_t |]
      FloatST  -> return [cty| float |]

    compLit _ a = case softwarePrimTypeOf a of
      BoolST  ->
        do addInclude "<stdbool.h>"
           return $ if a then [cexp| true |] else [cexp| false |]
      Int8ST   -> return [cexp| $a |]
      Int16ST  -> return [cexp| $a |]
      Int32ST  -> return [cexp| $a |]
      Int64ST  -> return [cexp| $a |]
      Word8ST  -> return [cexp| $a |]
      Word16ST -> return [cexp| $a |]
      Word32ST -> return [cexp| $a |]
      Word64ST -> return [cexp| $a |]
      FloatST  -> return [cexp| $a |]

instance CompExp Prim
  where
    compExp = compPrim

--------------------------------------------------------------------------------

compUnOp
  :: MonadC m
  => C.UnOp
  -> ASTF SoftwarePrimDomain a
  -> m C.Exp
compUnOp op a = do
  a' <- compPrim $ Prim a
  return $ C.UnOp op a' mempty

compBinOp
  :: MonadC m
  => C.BinOp
  -> ASTF SoftwarePrimDomain a
  -> ASTF SoftwarePrimDomain b
  -> m C.Exp
compBinOp op a b = do
  a' <- compPrim $ Prim a
  b' <- compPrim $ Prim b
  return $ C.BinOp op a' b' mempty  

compCast
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain b
  -> m C.Exp
compCast t a = do
  p <- compPrim $ Prim a
  case softwarePrimWitType t of
    Dict -> do
      typ <- compType (Proxy :: Proxy SoftwarePrimType) t
      return [cexp|($ty:typ) $p|]
      
compFun
  :: MonadC m
  => String
  -> Args (AST SoftwarePrimDomain) sig
  -> m C.Exp
compFun fun args = do
  as <- sequence $ listArgs (compPrim . Prim) args
  return [cexp| $id:fun($args:as) |]

compRotateL_def = [cedecl|
unsigned int feld_rotl(const unsigned int value, int shift) {
    if ((shift &= sizeof(value)*8 - 1) == 0)
      return value;
    return (value << shift) | (value >> (sizeof(value)*8 - shift));
}
|]

compRotateR_def = [cedecl|
unsigned int feld_rotr(const unsigned int value, int shift) {
    if ((shift &= sizeof(value)*8 - 1) == 0)
      return value;
    return (value >> shift) | (value << (sizeof(value)*8 - shift));
}
|]
    
--------------------------------------------------------------------------------

compPrim :: MonadC m => Prim a -> m C.Exp
compPrim = simpleMatch (\(s :&: t) -> go t s) . unPrim
  where
    go :: forall m sig
       .  MonadC m
       => SoftwarePrimTypeRep (DenResult sig)
       -> SoftwarePrimConstructs sig
       -> Args (AST SoftwarePrimDomain) sig
       -> m C.Exp
    go _ (FreeVar v) Nil = touchVar v >> return [cexp| $id:v |]
    go t (Lit a)     Nil | Dict <- softwarePrimWitType t
                         = compLit (Proxy :: Proxy SoftwarePrimType) a
                         
    go _ Neg (a :* Nil)      = compUnOp  C.Negate a
    go _ Add (a :* b :* Nil) = compBinOp C.Add a b
    go _ Sub (a :* b :* Nil) = compBinOp C.Sub a b
    go _ Mul (a :* b :* Nil) = compBinOp C.Mul a b
    go _ Div (a :* b :* Nil) = compBinOp C.Div a b
    go _ Mod (a :* b :* Nil) = compBinOp C.Mod a b

    go t I2N (a :* Nil) = compCast t a
    
    go _ Not (a :* Nil)      = compUnOp  C.Lnot a
    go _ And (a :* b :* Nil) = compBinOp C.Land a b
    go _ Or  (a :* b :* Nil) = compBinOp C.Lor  a b
    go _ Eq  (a :* b :* Nil) = compBinOp C.Eq   a b
    go _ Lt  (a :* b :* Nil) = compBinOp C.Lt   a b
    go _ Lte (a :* b :* Nil) = compBinOp C.Le   a b
    go _ Gt  (a :* b :* Nil) = compBinOp C.Gt   a b
    go _ Gte (a :* b :* Nil) = compBinOp C.Ge   a b

    go _ BitAnd   (a :* b :* Nil) = compBinOp C.And a b
    go _ BitOr    (a :* b :* Nil) = compBinOp C.Or  a b
    go _ BitXor   (a :* b :* Nil) = compBinOp C.Xor a b
    go _ BitCompl (a :* Nil)      = compUnOp  C.Not a
    go _ ShiftL   (a :* b :* Nil) = compBinOp C.Lsh a b
    go _ ShiftR   (a :* b :* Nil) = compBinOp C.Rsh a b
    
    go _ RotateL  (a :* b :* Nil) = do
      addGlobal compRotateL_def
      a' <- compPrim $ Prim a
      b' <- compPrim $ Prim b
      return [cexp| feld_rotl($a', $b') |]
    go _ RotateR  (a :* b :* Nil) = do
      addGlobal compRotateR_def
      a' <- compPrim $ Prim a
      b' <- compPrim $ Prim b
      return [cexp| feld_rotr($a', $b') |]
    
    go _ Sin args = addInclude "<tgmath.h>" >> compFun "sin" args
    go _ Cos args = addInclude "<tgmath.h>" >> compFun "cos" args
    go _ Tan args = addInclude "<tgmath.h>" >> compFun "tan" args

    go _ (ArrIx arr) (i :* Nil) =
      do i' <- compPrim $ Prim i
         touchVar arr
         return [cexp| $id:arr[$i'] |]

--------------------------------------------------------------------------------
