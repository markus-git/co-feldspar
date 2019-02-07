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
import Feldspar.Array.Vector hiding (reverse, (++))
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

import Prelude hiding (length, Word, (<=), (<), (>=))
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

assert :: SExp Bool -> String -> Software ()
assert = assertLabel $ UserAssertion ""

assertLabel :: AssertionLabel -> SExp Bool -> String -> Software ()
assertLabel lbl cond msg = Software $ Oper.singleInj $ Assert lbl cond msg

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
    slice from len (Arr o l arr) = Arr o' l' arr
      where
        o' = guardLabel InternalAssertion (from <= l)
               "arrSlice: index out of bounds." (o + from)
        l' = guardLabel InternalAssertion (from + len <= l)
               "arrSlice: slice to large." (len)

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
      = do assertLabel InternalAssertion
             (ix < length arr)
             "getArr: index out of bounds."
           Software
             $ fmap resugar
             $ mapStructA (flip getArr' (ix + arrOffset arr))
             $ unArr arr    
    setArr arr ix a
      = do assertLabel InternalAssertion
             (ix < length arr)
             "setArr: index out of bounds."
           Software
             $ sequence_
             $ zipListStruct
                 (\a' arr' -> setArr' arr' (ix + arrOffset arr) a')
                 (resugar a)
             $ unArr arr
    copyArr arr brr
      = do assertLabel InternalAssertion
             (length arr >= length brr)
             "copyArr: destination too small."
           Software
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
        index :: forall b . SoftwarePrimType b => Imp.IArr Index b -> SExp b
        index arr = sugarSymPrimSoftware
          (Guard InternalAssertion "arrIndex: index out of bounds.")
          (ix < len)
          (sugarSymPrimSoftware (ArrIx arr) (ix + off) :: SExp b)

instance Slicable SExp (IArr a)
  where
    slice from len (IArr o l arr) = IArr o' l' arr
      where
        o' = guardLabel InternalAssertion (from <= l)
               "arrSlice: index out of bounds." (o + from)
        l' = guardLabel InternalAssertion (from + len <= l)
               "arrSlice: slice to large." (len)

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
-- *** Assertions.

guard :: Syntax SExp a => SExp Bool -> String -> a -> a
guard = guardLabel $ UserAssertion ""

guardLabel :: Syntax SExp a => AssertionLabel -> SExp Bool -> String -> a -> a
guardLabel lbl cond msg = sugarSymSoftware (Guard lbl msg) cond

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

-- | Software argument specialized to software primitives.
type SArg = Argument SoftwarePrimType

-- | Establish a memory-mapping to a hardware signature.
mmap :: String -> HSig a -> Software (Address a)
mmap address sig =
  do pointer <- Software $ Oper.singleInj $ MMap address sig
     return $ Address pointer sig

-- | Call a memory-mapped component.
call :: Address a -> SArg (Soften a) -> Software ()
call address arg = Software $ Oper.singleInj $ Call address arg

-- | ...
nil :: SArg ()
nil = Nil

-- | ...
(>:) :: forall a b . (SType' a, HType' a, Integral a)
  => Ref (SExp a) -> SArg b -> SArg (Ref (SExp a) -> b)
(>:) = withHType' (Proxy :: Proxy a) ARef

-- | ...
(>>:) :: forall a b . (SType' a, HType' a, Integral a)
  => Arr (SExp a) -> SArg b -> SArg (Arr (SExp a) -> b)
(>>:) = withHType' (Proxy :: Proxy a) AArr

infixr 1 >:, >>:

--------------------------------------------------------------------------------
--
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
