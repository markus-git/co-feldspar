{-# language GADTs #-}
{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
{-# language FlexibleContexts #-}

module Feldspar.Software.Primitive.Backend where

import Feldspar.Software.Primitive

import Data.Complex (Complex (..))
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
      ComplexFloatST  -> addInclude "<tgmath.h>" >> return [cty| float  _Complex |]
      ComplexDoubleST -> addInclude "<tgmath.h>" >> return [cty| double _Complex |]

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
      ComplexFloatST  -> return $ compComplexLit a
      ComplexDoubleST -> return $ compComplexLit a

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
  compCastExp t p

compCastExp
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> C.Exp
  -> m C.Exp
compCastExp t p = case softwarePrimWitType t of
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
} |]

compRotateR_def = [cedecl|
unsigned int feld_rotr(const unsigned int value, int shift) {
    if ((shift &= sizeof(value)*8 - 1) == 0)
      return value;
    return (value >> shift) | (value << (sizeof(value)*8 - shift));
} |]

compComplexLit :: (Eq a, Num a, ToExp a) => Complex a -> C.Exp
compComplexLit (r :+ 0) = [cexp| $r |]
compComplexLit (0 :+ i) = [cexp| $i * I |]
compComplexLit (r :+ i) = [cexp| $r + $i * I |]
  
compAbs
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain a
  -> m C.Exp
compAbs t a 
 | boolType t    = error "compAbs: type BoolT not supported"
 | integerType t = addInclude "<stdlib.h>" >> compFun "abs" (a :* Nil)
 | wordType t    = compPrim $ Prim a
 | otherwise     = addInclude "<tgmath.h>" >> compFun "fabs" (a :* Nil)

compSign
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain a
  -> m C.Exp
compSign t a | boolType t = do
  error "compSign: type BoolST not supported"
compSign t a | integerType t = do
  addTagMacro
  a' <- compPrim $ Prim a
  return [cexp| TAG("signum", ($a' > 0) - ($a' < 0)) |]
compSign t a | wordType t = do
  addTagMacro
  a' <- compPrim $ Prim a
  return [cexp| TAG("signum", $a' > 0) |]
compSign FloatST a = do
  addTagMacro
  a' <- compPrim $ Prim a
  return [cexp| TAG("signum", (float) (($a' > 0) - ($a' < 0))) |]
compSign DoubleST a = do
  addTagMacro
  a' <- compPrim $ Prim a
  return [cexp| TAG("signum", (double) (($a' > 0) - ($a' < 0))) |]
compSign ComplexFloatST a = do
  addInclude "<complex.h>"
  addGlobal complexSignf_def
  a' <- compPrim $ Prim a
  return [cexp| feld_complexSignf($a') |]
compSign ComplexDoubleST a = do
  addInclude "<tgmath.h>"
  addGlobal complexSign_def
  a' <- compPrim $ Prim a
  return [cexp| feld_complexSign($a') |]
  -- todo: The floating point cases give `sign (-0.0) = 0.0`, which is (slightly)
  -- wrong. They should return -0.0. I don't know whether it's correct for other
  -- strange values.

complexSign_def = [cedecl|
double _Complex feld_complexSign(double _Complex c) {
    double z = cabs(c);
    if (z == 0)
      return 0;
    else
      return (creal(c)/z + I*(cimag(c)/z));
} |]

complexSignf_def = [cedecl|
float _Complex feld_complexSignf(float _Complex c) {
    float z = cabsf(c);
    if (z == 0)
      return 0;
    else
      return (crealf(c)/z + I*(cimagf(c)/z));
} |]

compDiv
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain a
  -> ASTF SoftwarePrimDomain b
  -> m C.Exp
compDiv Int64ST a b = do
  addGlobal ldiv_def
  compFun "feld_ldiv" (a :* b :* Nil)
compDiv t a b | integerType t = do
  addGlobal mod_def
  compFun "feld_mod" (a :* b :* Nil)
compDiv t a b | wordType t = do
  compBinOp C.Mod a b
compDiv t a b = do
  error $ "compDiv: type " ++ show t ++ " not supported"

ldiv_def = [cedecl|
long int feld_ldiv(long int x, long int y) {
    int q = x/y;
    int r = x%y;
    if ((r!=0) && ((r<0) != (y<0))) --q;
    return q;
} |]

mod_def = [cedecl|
int feld_mod(int x, int y) {
    int r = x%y;
    if ((r!=0) && ((r<0) != (y<0))) { r += y; }
    return r;
} |]

compMod
  :: MonadC m
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain a
  -> ASTF SoftwarePrimDomain b
  -> m C.Exp
compMod Int64ST a b = do
  addGlobal lmod_def
  compFun "feld_lmod" (a :* b :* Nil)
compMod t a b | integerType t = do
  addGlobal div_def
  compFun "feld_div" (a :* b :* Nil)
compMod t a b | wordType t = do
  compBinOp C.Mod a b
compMod t a b = do
  error $ "compMod: type " ++ show t ++ " not supported"

div_def = [cedecl|
int feld_div(int x, int y) {
    int q = x/y;
    int r = x%y;
    if ((r!=0) && ((r<0) != (y<0))) --q;
    return q;
} |]

lmod_def = [cedecl|
long int feld_lmod(long int x, long int y) {
    int r = x%y;
    if ((r!=0) && ((r<0) != (y<0))) { r += y; }
    return r;
} |]

compRound :: (SoftwarePrimType a, Num a, RealFrac b, MonadC m)
  => SoftwarePrimTypeRep a
  -> ASTF SoftwarePrimDomain b
  -> m C.Exp
compRound t a | integerType t || wordType t = do
  addInclude "<tgmath.h>"
  p <- compFun "lround" (a :* Nil)
  compCastExp t p
compRound t a | floatingType t || complexType t = do
  addInclude "<tgmath.h>"
  p <- compFun "round"  (a :* Nil)
  compCastExp t p
compRound t a = do
  error $ "compSign: type " ++ show t ++ " not supported"
  
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
                         
    go _ Neg  (a :* Nil)      = compUnOp  C.Negate a
    go _ Add  (a :* b :* Nil) = compBinOp C.Add a b
    go _ Sub  (a :* b :* Nil) = compBinOp C.Sub a b
    go _ Mul  (a :* b :* Nil) = compBinOp C.Mul a b
    go t Div  (a :* b :* Nil) = compDiv t a b
    go _ Quot (a :* b :* Nil) = compBinOp C.Div a b
    go _ Rem  (a :* b :* Nil) = compBinOp C.Mod a b
    go t Mod  (a :* b :* Nil) = compMod t a b
    go t Abs  (a :* Nil)      = compAbs t a
    go t Sign (a :* Nil)      = compSign t a
    go _ FDiv (a :* b :* Nil) = compBinOp C.Div a b

    go _ Exp   args = addInclude "<tgmath.h>" >> compFun "exp" args
    go _ Log   args = addInclude "<tgmath.h>" >> compFun "log" args
    go _ Sqrt  args = addInclude "<tgmath.h>" >> compFun "sqrt" args
    go _ Pow   args = addInclude "<tgmath.h>" >> compFun "pow" args

    go _ Sin   args = addInclude "<tgmath.h>" >> compFun "sin" args
    go _ Cos   args = addInclude "<tgmath.h>" >> compFun "cos" args
    go _ Tan   args = addInclude "<tgmath.h>" >> compFun "tan" args
    go _ Asin  args = addInclude "<tgmath.h>" >> compFun "asin" args
    go _ Acos  args = addInclude "<tgmath.h>" >> compFun "acos" args
    go _ Atan  args = addInclude "<tgmath.h>" >> compFun "atan" args
    go _ Sinh  args = addInclude "<tgmath.h>" >> compFun "sinh" args
    go _ Cosh  args = addInclude "<tgmath.h>" >> compFun "cosh" args
    go _ Tanh  args = addInclude "<tgmath.h>" >> compFun "tanh" args
    go _ Asinh args = addInclude "<tgmath.h>" >> compFun "asinh" args
    go _ Acosh args = addInclude "<tgmath.h>" >> compFun "acosh" args
    go _ Atanh args = addInclude "<tgmath.h>" >> compFun "atanh" args

    go t I2N   (a :* Nil) = compCast t a
    go t I2B   (a :* Nil) = compCast t a
    go t B2I   (a :* Nil) = compCast t a
    go t Round (a :* Nil) = compRound t a

    go _ Complex (a :* b :* Nil) = do
        addInclude "<tgmath.h>"
        a' <- compPrim $ Prim a
        b' <- compPrim $ Prim b
        return $ case (viewLitPrim a, viewLitPrim b) of
          (Just 0, _) -> [cexp| I*$b'       |]
          (_, Just 0) -> [cexp| $a'         |]
          _           -> [cexp| $a' + I*$b' |]

    go _ Polar (m :* p :* Nil)
        | Just 0 <- viewLitPrim m = do
            return [cexp| 0 |]
        | Just 0 <- viewLitPrim p = do
            m' <- compPrim $ Prim m
            return [cexp| $m' |]
        | Just 1 <- viewLitPrim m = do
            p' <- compPrim $ Prim p
            return [cexp| exp(I*$p') |]
        | otherwise = do
            m' <- compPrim $ Prim m
            p' <- compPrim $ Prim p
            return [cexp| $m' * exp(I*$p') |]

    go _ Real      args = addInclude "<tgmath.h>" >> compFun "creal" args
    go _ Imag      args = addInclude "<tgmath.h>" >> compFun "cimag" args
    go _ Magnitude args = addInclude "<tgmath.h>" >> compFun "cabs"  args
    go _ Phase     args = addInclude "<tgmath.h>" >> compFun "carg"  args
    go _ Conjugate args = addInclude "<tgmath.h>" >> compFun "conj"  args
    
    go _ Not (a :* Nil)      = compUnOp  C.Lnot a
    go _ And (a :* b :* Nil) = compBinOp C.Land a b
    go _ Or  (a :* b :* Nil) = compBinOp C.Lor  a b
    go _ Eq  (a :* b :* Nil) = compBinOp C.Eq   a b
    go _ Lt  (a :* b :* Nil) = compBinOp C.Lt   a b
    go _ Lte (a :* b :* Nil) = compBinOp C.Le   a b
    go _ Gt  (a :* b :* Nil) = compBinOp C.Gt   a b
    go _ Gte (a :* b :* Nil) = compBinOp C.Ge   a b

    go _ Pi Nil = addGlobal pi_def >> return [cexp| FELD_PI |]
      where pi_def = [cedecl|$esc:("#define FELD_PI 3.141592653589793")|]

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
    
    go _ (ArrIx arr) (i :* Nil) =
      do i' <- compPrim $ Prim i
         touchVar arr
         return [cexp| $id:arr[$i'] |]

--------------------------------------------------------------------------------

addTagMacro :: MonadC m => m ()
addTagMacro = addGlobal [cedecl| $esc:("#define TAG(tag,exp) (exp)") |]
  
boolType :: SoftwarePrimTypeRep a -> Bool
boolType BoolST     = True
boolType _          = False

integerType :: SoftwarePrimTypeRep a -> Bool
integerType Int8ST  = True
integerType Int16ST = True
integerType Int32ST = True
integerType Int64ST = True
integerType _       = False

wordType :: SoftwarePrimTypeRep a -> Bool
wordType Word8ST    = True
wordType Word16ST   = True
wordType Word32ST   = True
wordType Word64ST   = True
wordType _          = False

floatingType :: SoftwarePrimTypeRep a -> Bool
floatingType FloatST  = True
floatingType DoubleST = True
floatingType _        = False

complexType :: SoftwarePrimTypeRep a -> Bool
complexType ComplexFloatST  = True
complexType ComplexDoubleST = True
complexType _               = False

--------------------------------------------------------------------------------
