{-# language TypeFamilies          #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances  #-}
{-# language Rank2Types            #-}
{-# language ScopedTypeVariables   #-}

module Feldspar.Software.Frontend where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Array.Vector hiding (reverse)
import Feldspar.Array.Buffered (ArraysSwap(..))
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Feldspar.Software.Representation
import Data.Struct

import Data.Bits (Bits)
import Data.Constraint hiding (Sub)
import Data.Proxy
import Data.List (genericLength)
import Data.Word hiding (Word)

-- syntactic.
import Language.Syntactic (Syntactic(..))
import Language.Syntactic.Functional
import qualified Language.Syntactic as Syntactic

-- operational-higher.
import qualified Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import Language.Embedded.Imperative.Frontend.General hiding (Ref, Arr, IArr)
import qualified Language.Embedded.Imperative     as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- hardware-edsl.
import qualified Language.Embedded.Hardware.Command.CMD as Hard

-- hmm!
import Feldspar.Hardware.Primitive  (HardwarePrimType(..), HardwarePrimTypeRep(..))
import Feldspar.Hardware.Expression (HType')
import Feldspar.Hardware.Frontend   (HSig, withHType')

import Prelude hiding (length, Word, (<=))
import qualified Prelude

--------------------------------------------------------------------------------
-- * Expressions.
--------------------------------------------------------------------------------

instance Value SExp
  where
    value = sugarSymSoftware . Lit

instance Share SExp
  where
    share = sugarSymSoftware (Let "")

instance Loop SExp
  where
    loop = sugarSymSoftware ForLoop

instance Cond SExp
  where
    cond = sugarSymSoftware Cond

instance Equality SExp
  where
    (==) = sugarSymPrimSoftware Eq

instance Ordered SExp
  where
    (<)  = sugarSymPrimSoftware Lt
    (<=) = sugarSymPrimSoftware Lte
    (>)  = sugarSymPrimSoftware Gt
    (>=) = sugarSymPrimSoftware Gte

instance Logical SExp
  where
    not  = sugarSymPrimSoftware Not
    (&&) = sugarSymPrimSoftware And
    (||) = sugarSymPrimSoftware Or

instance Multiplicative SExp
  where
    mult = sugarSymPrimSoftware Mul
    div  = sugarSymPrimSoftware Div
    mod  = sugarSymPrimSoftware Mod

instance Bitwise SExp
  where
    complement = sugarSymPrimSoftware BitCompl
    (.&.) = sugarSymPrimSoftware BitAnd
    (.|.) = sugarSymPrimSoftware BitOr
    xor   = sugarSymPrimSoftware BitXor
    sll   = sugarSymPrimSoftware ShiftL
    srl   = sugarSymPrimSoftware ShiftR
    rol   = sugarSymPrimSoftware RotateL
    ror   = sugarSymPrimSoftware RotateR

instance Casting SExp
  where
    i2n = sugarSymPrimSoftware I2N

--------------------------------------------------------------------------------

instance (Bounded a, SType a) => Bounded (SExp a)
  where
    minBound = value minBound
    maxBound = value maxBound

instance (Num a, SType' a) => Num (SExp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSymPrimSoftware Add
    (-)         = sugarSymPrimSoftware Sub
    (*)         = sugarSymPrimSoftware Mul
    negate      = sugarSymPrimSoftware Neg
    abs         = error "todo: abs not implemeted for `SExp`"
    signum      = error "todo: signum not implemented for `SExp`"

--------------------------------------------------------------------------------
-- * Instructions.
--------------------------------------------------------------------------------

desugar :: (Syntactic a, Domain a ~ SoftwareDomain) => a -> SExp (Internal a)
desugar = SExp . Syntactic.desugar

sugar   :: (Syntactic a, Domain a ~ SoftwareDomain) => SExp (Internal a) -> a
sugar   = Syntactic.sugar . unSExp

resugar
  :: ( Syntactic a
     , Syntactic b
     , Internal a ~ Internal b
     , Domain a   ~ SoftwareDomain
     , Domain b   ~ SoftwareDomain
     )
  => a -> b
resugar = Syntactic.resugar

--------------------------------------------------------------------------------

instance References Software
  where
    type Reference Software = Ref    
    initRef = Software . fmap Ref . mapStructA (Imp.initRef) . resugar
    newRef  = Software . fmap Ref . mapStructA (const Imp.newRef) $ typeRep
    getRef  = Software . fmap resugar . mapStructA getRef' . unRef
    setRef ref
      = Software
      . sequence_
      . zipListStruct setRef' (unRef ref)
      . resugar
    unsafeFreezeRef
      = Software
      . fmap resugar
      . mapStructA freezeRef'
      . unRef

-- Imp.getRef specialized to software.
getRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
getRef' = withSType (Proxy :: Proxy b) Imp.getRef

-- Imp.setRef specialized to software.
setRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> SExp b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) ()
setRef' = withSType (Proxy :: Proxy b) Imp.setRef

-- 'Imp.unsafeFreezeRef' specialized to software.
freezeRef' :: forall b . SoftwarePrimType b => Imp.Ref b -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
freezeRef' = withSType (Proxy :: Proxy b) Imp.unsafeFreezeRef

--------------------------------------------------------------------------------

instance Slicable SExp (Arr a)
  where
    slice from len (Arr o l arr) = Arr (o+from) len arr

instance Finite SExp (Arr a)
  where
    length = arrLength

instance Arrays Software
  where
    type Array Software = Arr
    newArr len
      = Software
      $ fmap (Arr 0 len)
      $ mapStructA (const (Imp.newArr len))
      $ typeRep
    initArr elems
      = Software
      $ fmap (Arr 0 len . Node)
      $ Imp.constArr elems
      where len = value $ genericLength elems      
    getArr arr ix
      = Software
      $ fmap resugar
      $ mapStructA (flip getArr' (ix + arrOffset arr))
      $ unArr arr    
    setArr arr ix a
      = Software
      $ sequence_
      $ zipListStruct
         (\a' arr' -> setArr' arr' (ix + arrOffset arr) a')
         (resugar a)
      $ unArr arr
    copyArr arr brr
      = Software
      $ sequence_
      $ zipListStruct (\a b ->
          Imp.copyArr (a, arrOffset arr) (b, arrOffset brr) (length brr))
        (unArr arr)
        (unArr brr)

-- 'Imp.getArr' specialized to software.
getArr' :: forall b . SoftwarePrimType b
  => Imp.Arr Index b -> SExp Index
  -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) (SExp b)
getArr' = withSType (Proxy :: Proxy b) Imp.getArr

-- 'Imp.setArr' specialized to software.
setArr' :: forall b . SoftwarePrimType b
  => Imp.Arr Index b -> SExp Index -> SExp b
  -> Oper.Program SoftwareCMD (Oper.Param2 SExp SoftwarePrimType) ()
setArr' = withSType (Proxy :: Proxy b) Imp.setArr

--------------------------------------------------------------------------------

instance Syntax SExp a => Indexed SExp (IArr a)
  where
    type ArrElem (IArr a) = a
    (!) (IArr off len a) ix = resugar $ mapStruct index a
      where
        index :: SoftwarePrimType b => Imp.IArr Index b -> SExp b
        index arr = sugarSymPrimSoftware (ArrIx arr) (ix + off)

instance Slicable SExp (IArr a)
  where
    slice from len (IArr o l arr) = IArr (o+from) len arr

instance Finite SExp (IArr a)
  where
    length = iarrLength

instance IArrays Software
  where
    type IArray Software = IArr    
    unsafeFreezeArr arr
      = Software
      $ fmap (IArr (arrOffset arr) (length arr))
      $ mapStructA (Imp.unsafeFreezeArr)
      $ unArr arr
    unsafeThawArr iarr
      = Software
      $ fmap (Arr (iarrOffset iarr) (length iarr))
      $ mapStructA (Imp.unsafeThawArr)
      $ unIArr iarr

--------------------------------------------------------------------------------

-- | Short-hand for software pull vectors.
type SPull a = Pull SExp a

-- | Short-hand for software push vectors.
type SPush a = Push Software a

-- | Short-hand for software manifest vectors.
type SManifest a = Manifest Software a

instance Syntax SExp (SExp a) => Pushy Software (IArr (SExp a)) (SExp a)
  where
    toPush iarr = toPush (M iarr :: Manifest Software (SExp a))

instance ViewManifest Software (IArr (SExp a)) (SExp a)
  where
    viewManifest = Just . M

instance Manifestable Software (IArr (SExp a)) (SExp a)

--------------------------------------------------------------------------------

instance Control Software
  where
    iff c t f
      = Software
      $ Imp.iff (resugar c)
          (unSoftware t)
          (unSoftware f)      
    while c body
      = Software
      $ Imp.while
          (fmap resugar $ unSoftware c)
          (unSoftware body)
    for lower upper body
      = Software
      $ Imp.for
          (resugar lower, 1, Imp.Incl $ resugar upper)
          (unSoftware . body . resugar)

--------------------------------------------------------------------------------
-- ** Software instructions.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- *** File handling.

-- | Open a file.
fopen :: FilePath -> IOMode -> Software Handle
fopen file = Software . Imp.fopen file

-- | Close a file.
fclose :: Handle -> Software ()
fclose = Software . Imp.fclose

-- | Check for end of file.
feof :: Handle -> Software (SExp Bool)
feof = Software . Imp.feof

-- | Put a primitive value to a handle.
fput :: (Formattable a, SType' a)
    => Handle
    -> String  -- ^ Prefix.
    -> SExp a  -- ^ Expression to print.
    -> String  -- ^ Suffix.
    -> Software ()
fput h pre e post = Software $ Imp.fput h pre e post

-- | Get a primitive value from a handle.
fget :: (Formattable a, SType' a) => Handle -> Software (SExp a)
fget = Software . Imp.fget

-- | Handle to \stdin\.
stdin :: Handle
stdin = Imp.stdin

-- | Handle to \stdout\.
stdout :: Handle
stdout = Imp.stdout

--------------------------------------------------------------------------------
-- *** Printing.

class PrintfType r
  where
    fprf :: Handle -> String -> [Imp.PrintfArg SExp] -> r

instance (a ~ ()) => PrintfType (Software a)
  where
    fprf h form = Software . Oper.singleInj . Imp.FPrintf h form . reverse

instance (Formattable a, SType' a, PrintfType r) => PrintfType (SExp a -> r)
  where
    fprf h form as = \a -> fprf h form (Imp.PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: PrintfType r => Handle -> String -> r
fprintf h format = fprf h format []

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: PrintfType r => String -> r
printf = fprintf Imp.stdout

--------------------------------------------------------------------------------
-- *** Memory.

-- | ...
type SComp  = Address SoftwarePrimType

-- | ...
type SArg  = Argument SoftwarePrimType

mmap :: String -> HSig a -> Software (SComp (Soften a))
mmap addr sig =
  do ref <- Software $ Oper.singleInj $ MMap addr sig
     return $ soften ref sig
  where
    soften :: String -> HSig b -> SComp (Soften b)
    soften _ (Hard.Ret _) = Ret
    soften r (Hard.SSig _ m (sf :: Hard.Signal c -> HSig d)) =
      case witSP (Proxy::Proxy c) of
        Dict -> SRef r m $ \ref -> soften r $ sf $ error "evaluated soften."
      where
        witSP :: forall a . HardwarePrimType a
          => Proxy a -> Dict (SoftwarePrimType a)
        witSP _ = case hardwareRep :: HardwarePrimTypeRep a of
          BoolHT    -> Dict
          Int8HT    -> Dict
          Int16HT   -> Dict
          Int32HT   -> Dict
          Int64HT   -> Dict
          Word8HT   -> Dict
          Word16HT  -> Dict
          Word32HT  -> Dict
          Word64HT  -> Dict

call :: SComp a -> SArg a -> Software ()
call addr arg = Software $ Oper.singleInj $ Call addr arg

empty :: SArg ()
empty = Nil

(.+.) :: forall a b . (SType' a, HType' a, Integral a)
  => Ref (SExp a) -> SArg b -> SArg (Ref (SExp a) -> b)
(.+.) = withHType' (Proxy::Proxy a) ARef

infixr 1 .+.

--------------------------------------------------------------------------------

-- Swap an `Imp.FreePred` constraint with a `SoftwarePrimType` one.
withSType :: forall a b . Proxy a
  -> (Imp.FreePred SExp a => b)
  -> (SoftwarePrimType  a => b)
withSType _ f = case predicateDict (softwareRep :: SoftwarePrimTypeRep a) of
  Dict -> f

-- Proves that a type from `SoftwarePrimTypeRep` satisfies `Imp.FreePred`.
predicateDict :: SoftwarePrimTypeRep a -> Dict (Imp.FreePred SExp a)
predicateDict rep = case rep of
  BoolST   -> Dict
  Int8ST   -> Dict
  Int16ST  -> Dict
  Int32ST  -> Dict
  Int64ST  -> Dict
  Word8ST  -> Dict
  Word16ST -> Dict
  Word32ST -> Dict
  Word64ST -> Dict
  FloatST  -> Dict

--------------------------------------------------------------------------------
