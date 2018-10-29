{-# language GADTs                      #-}
{-# language ConstraintKinds            #-}
{-# language TypeOperators              #-}
{-# language TypeFamilies               #-}
{-# language MultiParamTypeClasses      #-}
{-# language FlexibleContexts           #-}
{-# language FlexibleInstances          #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language PolyKinds                  #-}

{-# language ScopedTypeVariables #-}
{-# language Rank2Types #-}
{-# language DataKinds #-}

module Feldspar.Software.Representation where

import Feldspar.Sugar
import Feldspar.Representation
import Feldspar.Frontend
import Feldspar.Storable
import Feldspar.Array.Buffered (ArraysEq(..))
import Feldspar.Software.Primitive
import Feldspar.Software.Expression
import Data.Struct

import qualified Feldspar.Verify.Monad as V
import qualified Feldspar.Verify.SMT   as SMT
import qualified Data.Map.Strict       as Map
import qualified Control.Monad.RWS.Strict as S

import Data.Array (Ix)
import Data.Maybe (fromMaybe)
import Data.Int
import Data.Word
import Data.List (genericTake, (\\))
import Data.Typeable (Typeable, cast)
import Data.Constraint hiding ((\\))
import Control.Monad.Reader (ReaderT(..), runReaderT, lift)

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam)
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp

-- hardware-edsl.
import Language.Embedded.Hardware.Command (Signal, Mode)
import qualified Language.Embedded.Hardware.Command as Hard
import qualified Language.Embedded.Hardware.Expression.Represent as Hard

import Prelude hiding ((==))
import qualified Prelude as P

-- hmm!
import Feldspar.Hardware.Frontend (HSig)

--------------------------------------------------------------------------------
-- * Programs.
--------------------------------------------------------------------------------

data AssertCMD fs a
  where
    Assert :: AssertionLabel
           -> exp Bool
           -> String
           -> AssertCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor AssertCMD
  where
    hfmap _ (Assert lbl cond msg) = Assert lbl cond msg

instance Oper.HBifunctor AssertCMD
  where
    hbimap _ g (Assert lbl cond msg) = Assert lbl (g cond) msg

instance Oper.InterpBi AssertCMD IO (Oper.Param1 SoftwarePrimType)
  where
    interpBi (Assert _ cond msg) = do
      cond' <- cond
      unless cond' $ error $ "Assertion failed: " ++ msg

--------------------------------------------------------------------------------

-- | Soften the hardware signature of a component into a type that uses the
--   correspoinding data types in software.
type family Soften a where
  Soften ()                   = ()
  Soften (Hard.Signal  a -> b) = Ref (SExp a) -> Soften b
  Soften (Hard.Array i a -> b) = Arr (SExp a) -> Soften b

-- | Software argument for a hardware component.
data Argument pred a
  where
    Nil  :: Argument pred ()
    ARef :: (pred a, Integral a, Hard.PrimType a)
         => Ref (SExp a)
         -> Argument pred b
         -> Argument pred (Ref (SExp a) -> b)
    AArr :: (pred a, Integral a, Hard.PrimType a)
         => Arr (SExp a)
         -> Argument pred b
         -> Argument pred (Arr (SExp a) -> b)

-- | Software component, consists of a hardware signature and its address.
data Address a = Address String (HSig a)

-- | ...
data MMapCMD fs a
  where
    MMap :: String
         -> HSig a
         -> MMapCMD (Oper.Param3 prog exp pred) String
    Call :: Address a
         -> Argument pred (Soften a)
         -> MMapCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor MMapCMD
  where
    hfmap f (MMap s sig)    = MMap s sig
    hfmap f (Call addr arg) = Call addr arg

instance Oper.HBifunctor MMapCMD
  where
    hbimap g f (MMap s sig)    = MMap s sig
    hbimap g f (Call addr arg) = Call addr arg

instance (MMapCMD Oper.:<: instr) => Oper.Reexpressible MMapCMD instr env
  where
    reexpressInstrEnv reexp (MMap s sig)    = lift $ singleInj $ MMap s sig
    reexpressInstrEnv reexp (Call addr arg) = lift $ singleInj $ Call addr arg

instance Oper.InterpBi MMapCMD IO (Param1 SoftwarePrimType)
  where
    interpBi = error "todo: interpBi of mmap."

--------------------------------------------------------------------------------

-- | Software instructions.
type SoftwareCMD
    -- ^ Computational instructions.
         = Imp.RefCMD
  Oper.:+: Imp.ControlCMD
  Oper.:+: Imp.ArrCMD
    -- ^ Software specific instructions.
  Oper.:+: Imp.FileCMD
  Oper.:+: AssertCMD  
  Oper.:+: MMapCMD

-- | Monad for building software programs in Feldspar.
newtype Software a = Software { unSoftware ::
    Program SoftwareCMD (Param2 SExp SoftwarePrimType) a }
  deriving (Functor, Applicative, Monad)

type instance Expr     Software = SExp
type instance DomainOf Software = SoftwareDomain

--------------------------------------------------------------------------------

-- | Software reference.
newtype Ref a = Ref { unRef :: Struct SoftwarePrimType Imp.Ref (Internal a) }

-- | Software array.
data Arr a = Arr
  { arrOffset :: SExp Index
  , arrLength :: SExp Length
  , unArr     :: Struct SoftwarePrimType (Imp.Arr Index) (Internal a)
  }

-- | Immutable software array.
data IArr a = IArr
  { iarrOffset :: SExp Index
  , iarrLength :: SExp Length
  , unIArr     :: Struct SoftwarePrimType (Imp.IArr Index) (Internal a)
  }

--------------------------------------------------------------------------------
-- ** ...
--------------------------------------------------------------------------------

-- | Bindings for values.
data ValueBinding exp a = ValueBinding {
    vb_value     :: V.SMTExpr exp a
  , vb_reference :: Maybe String
  }
  deriving (Eq, Ord, Show, Typeable)

instance V.SMTEval exp a => V.Mergeable (ValueBinding exp a)
  where
    merge cond (ValueBinding _ (Just l)) (ValueBinding _ (Just r))
      | l P./= r = error "immutable binding bound in two locations"
    merge cond l r = ValueBinding {
        vb_value     = V.merge cond (vb_value l) (vb_value r)
      , vb_reference = (vb_reference l) `mplus` (vb_reference r)
      }

instance V.SMTEval exp a => V.ShowModel (ValueBinding exp a)
  where
    showModel = V.showModel . vb_value

instance V.SMTEval exp a => V.Fresh (ValueBinding exp a)
  where
    fresh name = V.fresh name >>= return . flip ValueBinding Nothing

instance V.SMTEval exp a => V.IsLiteral (V.Literal (ValueBinding exp a))

instance V.SMTEval exp a => V.Invariant (ValueBinding exp a)
  where
    data Literal (ValueBinding exp a) = LitVB
      deriving (Eq, Ord, Show, Typeable)

instance V.SMTEval exp a => V.Exprs (ValueBinding exp a)
  where
    exprs val = V.toSMT (vb_value val) : []

-- | ...
peekValue :: forall exp a . V.SMTEval exp a => String -> V.Verify (V.SMTExpr exp a)
peekValue name =
  do ValueBinding val ref <- V.peek name
     V.warning () $ case ref of
       Nothing -> return ()
       Just rn ->
         do ref <- V.peek rn :: V.Verify (ReferenceBinding exp a)
            ok  <- V.provable "ref. not frozen" $ val V..==. rb_value ref
            unless ok $ V.warn $ "unsafe use of frozen ref. " ++ name
     return val

-- | ...
pokeValue :: V.SMTEval exp a => String -> V.SMTExpr exp a -> V.Verify ()
pokeValue name val = V.poke name (ValueBinding val Nothing)

--------------------------------------------------------------------------------

data ReferenceBinding exp a = ReferenceBinding {
    rb_value :: V.SMTExpr exp a
  , rb_init  :: SMT.SExpr
  }
  deriving (Eq, Ord, Show, Typeable)

instance V.SMTEval exp a => V.Mergeable (ReferenceBinding exp a)
  where
    merge cond (ReferenceBinding vl rl) (ReferenceBinding vr rr) =
      ReferenceBinding (V.merge cond vl vr) (V.merge cond rl rr)

instance V.SMTEval exp a => V.ShowModel (ReferenceBinding exp a)
  where
    showModel = V.showModel . rb_value

instance V.SMTEval exp a => V.Fresh (ReferenceBinding exp a)
  where
    fresh name =
      do val  <- V.fresh name
         init <- V.freshVar (name ++ ".init") SMT.tBool
         return $ ReferenceBinding val init

instance V.SMTEval exp a => V.IsLiteral (V.Literal (ReferenceBinding exp a))
  where
    smtLit _ new (ReferenceInit name) = rb_init ref
      where
        ref :: ReferenceBinding exp a
        ref = V.lookupContext name new
    smtLit old new (ReferenceSame name) = rb_init refNew `SMT.eq` rb_init refOld
      where
        refNew, refOld :: ReferenceBinding exp a
        refNew = V.lookupContext name new
        refOld = V.lookupContext name old

instance V.SMTEval exp a => V.Invariant (ReferenceBinding exp a)
  where
    data Literal (ReferenceBinding exp a) =
        ReferenceInit String
      | ReferenceSame String
      deriving (Eq, Ord, Show, Typeable)
    
    literals name _ = ReferenceInit name : ReferenceSame name : []

instance V.SMTEval exp a => V.Exprs (ReferenceBinding exp a)
  where
    exprs val = V.toSMT (rb_value val) : []

-- | ...
newReference :: V.SMTEval exp a => String -> exp a -> V.Verify ()
newReference name (_ :: exp a) =
  do ref <- V.fresh name
     V.poke name (ref { rb_init = SMT.bool False } :: ReferenceBinding exp a)

-- | ...
getReference :: V.SMTEval exp a => String -> V.Verify (V.SMTExpr exp a)
getReference name =
  do ref <- V.peek name
     V.warning () $
       do ok <- V.provable "ref. initialised" $ rb_init ref
          unless ok $ V.warn $ "ref. " ++ name ++ " read before initialisation"
     return $ rb_value ref

-- | ...
setReference :: forall exp a . V.SMTEval exp a => String -> V.SMTExpr exp a ->
  V.Verify ()
setReference name val = do
  ref <- V.peek name :: V.Verify (ReferenceBinding exp a)
  V.poke name ref { rb_value = val, rb_init = SMT.bool True}

-- | ...
unsafeFreezeReference :: forall exp a . V.SMTEval exp a => String -> String ->
  exp a -> V.Verify ()
unsafeFreezeReference nameRef nameVal (_ :: exp a) =
  do ref <- V.peek nameRef :: V.Verify (ReferenceBinding exp a)
     V.poke nameRef (ValueBinding (rb_value ref) (Just nameRef))

--------------------------------------------------------------------------------

-- | A wrapper to help with fresh name generation.
newtype SMTArray exp i a = SMTArray SMT.SExpr
  deriving (Eq, Ord, Show, V.Mergeable)

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Fresh (SMTArray exp i a)
  where
    fresh = V.freshSExpr

instance (V.SMTEval exp a, V.SMTEval exp i) => V.TypedSExpr (SMTArray exp i a)
  where
    smtType _ = SMT.tArray
      (V.smtType (undefined :: V.SMTExpr exp i))
      (V.smtType (undefined :: V.SMTExpr exp a))
    toSMT (SMTArray arr) = arr
    fromSMT arr = SMTArray arr

-- | A binding that represents the contents of an array.
data ArrayContents exp i a = ArrayContents {
    ac_value :: SMTArray exp i a
  , ac_bound :: V.SMTExpr exp i
  }
  deriving (Eq, Ord, Typeable, Show)

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Mergeable (ArrayContents exp i a)
  where
    merge cond (ArrayContents vl bl) (ArrayContents vr br) =
      ArrayContents (V.merge cond vl vr) (V.merge cond bl br)

instance (V.SMTEval exp a, V.SMTEval exp i) => V.ShowModel (ArrayContents exp i a)
  where
    showModel arr = lift $ do
      bound <- SMT.getExpr (V.toSMT (ac_bound arr))
      SMT.showArray bound (V.toSMT (ac_value arr))

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Fresh (ArrayContents exp i a)
  where
    fresh name = do
      value <- V.fresh (name ++ ".value")
      bound <- V.fresh (name ++ ".bound")
      return $ ArrayContents value bound

instance (V.SMTEval exp a, V.SMTEval exp i) =>
  V.IsLiteral (V.Literal (ArrayContents exp i a))

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Invariant (ArrayContents exp i a)
  where
    data Literal (ArrayContents exp i a) = LitAC
      deriving (Eq, Ord, Show, Typeable)

    havoc name arr = do
      value <- V.fresh name
      return $ ArrayContents { ac_value = value, ac_bound = ac_bound arr }

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Exprs (ArrayContents exp i a)
  where
    exprs arr = V.toSMT (ac_bound arr) : V.toSMT (ac_value arr) : []

-- | A binding that represents a reference to an array.
data ArrayBinding exp i a = ArrayBinding {
    arr_source     :: Maybe String
  , arr_accessible :: SMT.SExpr
  , arr_readable   :: SMT.SExpr
  , arr_failed     :: SMT.SExpr
  }
  deriving (Eq, Ord, Typeable, Show)

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Mergeable (ArrayBinding exp i a)
  where
    merge cond (ArrayBinding sl al rl fl) (ArrayBinding sr ar rr fr) =
      ArrayBinding
        (sl `mplus` sl)
        (V.merge cond al ar)
        (V.merge cond rl rr)
        (V.merge cond fl fr)

instance (V.SMTEval exp a, V.SMTEval exp i) => V.ShowModel (ArrayBinding exp i a)
  where
    showModel (ArrayBinding {arr_source = Nothing}) =
      return "<unbound array>"
    showModel (ArrayBinding {arr_source = Just source}) =
      (V.peek source :: V.Verify (ArrayContents exp i a)) >>= V.showModel

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Exprs (ArrayBinding exp i a)
  where
    exprs (ArrayBinding _ a r f) = [a, r, f]

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Fresh (ArrayBinding exp i a)
  where
    fresh name =
      do accessible <- V.freshVar (name ++ ".ok") SMT.tBool
         readable   <- V.freshVar (name ++ ".read") SMT.tBool
         failed     <- V.freshVar (name ++ ".failed") SMT.tBool
         return $ ArrayBinding Nothing accessible readable failed

instance (V.SMTEval exp a, V.SMTEval exp i) =>
    V.IsLiteral (V.Literal (ArrayBinding exp i a))
  where
    smtLit _ new (ArrayAccessible name) =
      arr_accessible (V.lookupContext name new :: ArrayBinding exp i a)
    smtLit _ new (ArrayReadable name) =
      arr_readable (V.lookupContext name new :: ArrayBinding exp i a)
    smtLit old new (ArraySafetyPreserved name) =
      case V.maybeLookupContext name old of
        Just (arr :: ArrayBinding exp i a) -> arr_failed arr SMT..||.
          SMT.not (arr_failed (V.lookupContext name new :: ArrayBinding exp i a))
        Nothing -> SMT.bool False

instance (V.SMTEval exp a, V.SMTEval exp i) => V.Invariant (ArrayBinding exp i a)
  where
    data Literal (ArrayBinding exp i a) =
        ArrayAccessible String
      | ArrayReadable String
      | ArraySafetyPreserved String
      deriving (Eq, Ord, Show, Typeable)

    literals name _ = ArrayAccessible name
                    : ArrayReadable name
                    : ArraySafetyPreserved name
                    : []

    havoc name src =
      do arr <- V.fresh name :: V.Verify (ArrayBinding exp i a)
         return arr { arr_source = arr_source src }

    warns1 ctx name arr = arr { arr_failed = SMT.bool False }
    warns2 ctx name arr = arr {
        arr_accessible = arr_accessible brr
      , arr_readable = arr_readable brr
      , arr_failed = arr_failed brr
      }
      where
        brr :: ArrayBinding exp i a
        brr = V.lookupContext name ctx

    warnLiterals name arr =
          (ArrayAccessible name, ok)
        : (ArrayReadable name, ok)
        : []
      where ok = SMT.not (arr_failed arr)
    warnLiterals2 name _ = ArraySafetyPreserved name : []

-- | ...
arrayBindings :: Typeable (ArrayBinding exp i a) => V.Context -> String ->
  [(String, ArrayBinding exp i a)]
arrayBindings ctx name = filter pred
  [ (name', y)
  | (V.Name name' _, V.Entry x) <- Map.toList ctx
  , Just y <- [cast x]
  ]
  where
    pred :: (String, ArrayBinding exp i a) -> Bool
    pred (_, arr) = arr_source arr P.== Just name

-- | ...
selectArray :: (V.SMTEval exp a, V.SMTEval exp i) => SMTArray exp i a ->
  V.SMTExpr exp i -> V.SMTExpr exp a
selectArray arr i = V.fromSMT (SMT.select (V.toSMT arr) (V.toSMT i))

-- | ...
storeArray :: (V.SMTEval exp a, V.SMTEval exp i) => V.SMTExpr exp i ->
  V.SMTExpr exp a -> SMTArray exp i a -> SMTArray exp i a
storeArray i x arr = V.fromSMT (SMT.store (V.toSMT arr) (V.toSMT i) (V.toSMT x))

newArray :: forall exp i a .
  ( Num (V.SMTExpr exp i)
  , V.SMTOrd (V.SMTExpr exp i)
  , V.SMTEval exp i
  , V.SMTEval exp a
  ) => String -> V.SMTExpr exp i -> V.Verify (SMTArray exp i a)
newArray name n = do
  value <- V.fresh name :: V.Verify (SMTArray exp i a)
  let arr :: ArrayBinding exp i a
      arr = ArrayBinding
              (Just name)
              (SMT.bool True)
              (SMT.bool True)
              (SMT.bool False)
  V.poke name (ArrayContents value n)
  V.poke name arr
  return value

peekArray :: forall exp i a .
  ( V.SMTEval exp i
  , V.SMTEval exp a
  ) => String -> V.Verify (Maybe (
      ArrayBinding exp i a
    , String
    , ArrayContents exp i a))
peekArray name =
  do ctx <- S.get
     arr <- V.peek name
     ok  <- V.provable "array accessible" (arr_accessible arr)
     if ok then
       do let
            source = fromMaybe
              (error "array accessible but has no source")
              (arr_source arr)
          src <- V.peek source
          return (Just (arr, source, src))
     else
       do -- invalidate everything to help with computing the frame
          V.warn ("unsafe use of inaccessible array " ++ name)
          let
            refs = case arr_source arr of
              Nothing  -> (name, arr) : []
              Just src -> arrayBindings ctx src
          forM_ refs $ \(name, arr) ->
            do arr <- V.havoc name arr
               V.poke name (
                 arr { arr_failed = SMT.bool True } :: ArrayBinding exp i a)
          return Nothing

readArray :: forall exp i a .
  ( V.SMTOrd (V.SMTExpr exp i)
  , Ix i
  , V.SMTEval exp i
  , V.SMTEval exp a
  ) => String -> V.SMTExpr exp i -> V.Verify (V.SMTExpr exp a)
readArray name ix = do
  hintArr ix
  marr <- peekArray name
  case marr of
    Nothing -> V.fresh "unbound"
    Just (arr :: ArrayBinding exp i a, _, src) ->
      do V.warning () $
           do ok <- V.provable "array not modified" $
                SMT.not (ix V..==. V.skolemIndex) SMT..||. arr_readable arr
              unless ok $
                do V.warn ("Unsafe use of frozen array " ++ name)
                   V.poke name (
                     arr { arr_failed = SMT.bool True } :: ArrayBinding exp i a)
         return (selectArray (ac_value src) ix)

updateArray :: forall exp i a . (Ix i, V.SMTEval exp i, V.SMTEval exp a) =>
  String ->
  (SMTArray exp i a -> SMTArray exp i a) ->
  (V.SMTExpr exp i -> SMT.SExpr) ->
  V.Verify ()
updateArray name update touched =
  do marr <- peekArray name
     case marr of
       Nothing -> return ()
       Just (arr :: ArrayBinding exp i a, source, src) ->
         do ctx <- S.get
            forM_ (arrayBindings ctx source \\ [(name, arr)]) $ \(name, arr) ->
              do let
                   readable = SMT.not (touched V.skolemIndex) SMT..&&.
                     arr_readable arr
                 V.poke name (
                   arr { arr_readable = readable } :: ArrayBinding exp i a)
            V.poke name (
              arr { arr_readable = SMT.bool True } :: ArrayBinding exp i a)
            V.poke source (
              src { ac_value = update (ac_value src) } :: ArrayContents exp i a)

hintArr :: forall exp i . (V.SMTEval exp i, V.SMTOrd (V.SMTExpr exp i), Ix i) =>
  V.SMTExpr exp i -> V.Verify ()
hintArr ix =
  do V.hintFormula (ix V..<. V.skolemIndex)
     V.hintFormula (ix V..>. V.skolemIndex)

--------------------------------------------------------------------------------
-- ** ...
--------------------------------------------------------------------------------

withWitness :: forall instr prog exp pred a b .
  (V.SMTEval1 exp, V.Pred exp a) =>
  a ->
  instr '(prog, Param2 exp pred) b ->
  (V.SMTEval exp a => V.Verify ()) ->
  V.Verify (instr '(prog, Param2 exp pred) b)
withWitness (x :: a) instr m
  | Dict <- V.witnessPred (undefined :: exp a) = m >> return instr

producesValue :: forall instr prog exp pred a .
  (V.SMTEval1 exp, V.Pred exp a, V.Pred exp ~ pred) =>
  instr '(prog, Param2 exp pred) (Imp.Val a) ->
  Imp.Val a ->
  V.Verify (instr '(prog, Param2 exp pred) (Imp.Val a))
producesValue instr (Imp.ValComp name :: Imp.Val a) =
  withWitness (undefined :: a) instr $
    do val <- V.fresh name
       pokeValue name (val :: V.SMTExpr exp a)

--------------------------------------------------------------------------------

instance (V.SMTEval1 exp, V.Pred exp ~ pred) =>
    V.VerifyInstr Imp.RefCMD exp pred
  where
    verifyInstr i@(Imp.NewRef _) (Imp.RefComp name :: Imp.Ref a) =
      withWitness (undefined :: a) i $
        do newReference name (undefined :: exp a)
    verifyInstr i@(Imp.InitRef _ exp) (Imp.RefComp name :: Imp.Ref a) =
      withWitness (undefined :: a) i $
        do newReference name (undefined :: exp a)
           val <- V.eval exp
           setReference name val
    verifyInstr i@(Imp.GetRef (Imp.RefComp ref)) (Imp.ValComp name :: Imp.Val a) =
      withWitness (undefined :: a) i $
        do val :: V.SMTExpr exp a <- getReference ref
           pokeValue name val
    verifyInstr i@(Imp.SetRef (Imp.RefComp ref :: Imp.Ref a) exp) () =
      withWitness (undefined :: a) i $
        do val <- V.eval exp
           setReference ref val
    verifyInstr i@(Imp.UnsafeFreezeRef (Imp.RefComp ref)) (Imp.ValComp name :: Imp.Val a) =
      withWitness (undefined :: a) i $
        do unsafeFreezeReference ref name (undefined :: exp a)

--------------------------------------------------------------------------------

instance (V.SMTEval1 exp, V.Pred exp ~ pred) =>
    V.VerifyInstr Imp.ArrCMD exp pred
  where
    verifyInstr i@(Imp.NewArr _ n) a@(Imp.ArrComp name :: Imp.Arr i a)
      | Dict <- V.witnessPred (undefined :: exp i)
      , Dict <- V.witnessNum  (undefined :: exp i)
      , Dict <- V.witnessOrd  (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do len <- V.eval n
           arr <- newArray name len :: V.Verify (SMTArray exp i a)
           return ()
    verifyInstr i@(Imp.ConstArr _ xs) a@(Imp.ArrComp name :: Imp.Arr i a)
      | Dict <- V.witnessPred (undefined :: exp i)
      , Dict <- V.witnessNum  (undefined :: exp i)
      , Dict <- V.witnessOrd  (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do let
             is  :: [V.SMTExpr exp i]
             is  = map V.fromConstant [0..]
             ys  :: [V.SMTExpr exp a]
             ys  = map V.fromConstant xs
             len :: Num b => b
             len = fromIntegral (P.length xs)
           arr :: SMTArray exp i a <- newArray name len
           forM_ (P.zip is ys) $ \(i, y) ->
             V.assume "array initialisation" (selectArray arr i V..==. y)
    verifyInstr i@(Imp.GetArr (Imp.ArrComp arr :: Imp.Arr i a) ix) (Imp.ValComp name)
      | Dict <- V.witnessPred (undefined :: exp i)
      , Dict <- V.witnessOrd  (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do ix' <- V.eval ix
           val :: V.SMTExpr exp a <- readArray arr ix'
           pokeValue name val
    verifyInstr i@(Imp.SetArr (Imp.ArrComp arr :: Imp.Arr i a) ix val) ()
      | Dict <- V.witnessPred (undefined :: exp i)
      , Dict <- V.witnessOrd  (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do ix'  <- V.eval ix
           val' <- V.eval val
           updateArray arr (storeArray ix' val') (V..==. ix')
           hintArr ix'
    verifyInstr i@(Imp.CopyArr (Imp.ArrComp dest :: Imp.Arr i a, destOffs) (Imp.ArrComp src, srcOffs) len) ()
      | Dict <- V.witnessPred (undefined :: exp i)
      , Dict <- V.witnessNum  (undefined :: exp i)
      , Dict <- V.witnessOrd  (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do dest' :: ArrayBinding exp i a <- V.peek dest
           src'  :: ArrayBinding exp i a <- V.peek src
           destOffs' <- V.eval destOffs
           srcOffs'  <- V.eval srcOffs
           len'      <- V.eval len
           ix :: V.SMTExpr exp i <- V.fresh "index"
           V.assume "index in bounds" $
             (len' V..<=. 0) SMT..||.
             (srcOffs' V..<=. ix) SMT..&&. (ix V..<. (destOffs' + len'))
           val :: V.SMTExpr exp a <- readArray src ix
           -- todo: interpret destination array.
           dest' :: SMTArray exp i a <- V.fresh "copy"
           updateArray dest (P.const dest') $ \i ->
             (destOffs' V..<=. i) SMT..&&. (i V..<. (destOffs' + len'))
    verifyInstr i@(Imp.UnsafeFreezeArr (Imp.ArrComp arr :: Imp.Arr i a)) (Imp.IArrComp name)
      | Dict <- V.witnessPred (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do arr' :: ArrayBinding exp i a <- V.peek name
           V.poke name arr'
    verifyInstr i@(Imp.UnsafeThawArr (Imp.IArrComp iarr :: Imp.IArr i a)) (Imp.ArrComp name)
      | Dict <- V.witnessPred (undefined :: exp i) =
      withWitness (undefined :: a) i $
        do iarr' :: ArrayBinding exp i a <- V.peek name
           V.poke name iarr'

--------------------------------------------------------------------------------

instance (V.SMTEval1 exp, V.Pred exp ~ pred) =>
    V.VerifyInstr Imp.FileCMD exp pred
  where
    verifyInstr i@(Imp.FPrintf _ _ as) _ =
      do let
           evalArg :: Imp.PrintfArg exp pred -> V.Verify ()
           evalArg (Imp.PrintfArg (exp :: exp a)) =
             case V.witnessPred (undefined :: exp a) of
               Dict -> void (V.eval exp)
         mapM_ evalArg as
         return i
    verifyInstr i@(Imp.FGet{}) val = producesValue i val
    verifyInstr i _ = return i

--------------------------------------------------------------------------------
-- **
--------------------------------------------------------------------------------

instance ArraysEq Arr IArr
  where
    unsafeArrEq (Arr _ _ arr) (IArr _ _ brr) =
      and (zipListStruct sameId arr brr)
      where
        sameId :: Imp.Arr Index a -> Imp.IArr Index a -> Bool
        sameId (Imp.ArrComp a) (Imp.IArrComp b) = a P.== b
        sameId _ _ = False

--------------------------------------------------------------------------------

instance (Reference Software ~ Ref, Type SoftwarePrimType a) =>
    Storable Software (SExp a)
  where
    type StoreRep Software (SExp a) = Ref (SExp a)
    type StoreSize Software (SExp a) = ()
    newStoreRep _ _      = newRef
    initStoreRep         = initRef
    readStoreRep         = getRef
    unsafeFreezeStoreRep = unsafeFreezeRef
    writeStoreRep        = setRef

--------------------------------------------------------------------------------
