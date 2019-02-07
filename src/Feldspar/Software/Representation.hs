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

import qualified Control.Monad.FirstOrder as FO

import Feldspar.Verify.Monad (Verify)
import qualified Feldspar.Verify.Monad    as V
import qualified Feldspar.Verify.SMT      as SMT
import qualified Feldspar.Verify.Abstract as A
import qualified Data.Map.Strict          as Map
import qualified Control.Monad.RWS.Strict as S

import Control.Monad.Identity

import Data.Array (Ix)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Ord
import Data.IORef
import Data.Int
import Data.Word
import Data.List (genericTake, (\\), sort, sortBy, group, groupBy, intersect, nub)
import Data.Typeable (Typeable, cast, typeOf)
import Data.Constraint hiding ((\\))
import Control.Monad.Reader (ReaderT(..), runReaderT, lift)

-- syntactic.
import Language.Syntactic hiding (Signature, Args)
import Language.Syntactic.Functional hiding (Lam, Var)
import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

-- operational-higher.
import Control.Monad.Operational.Higher as Oper

-- imperative-edsl.
import qualified Language.Embedded.Expression as Imp
import qualified Language.Embedded.Imperative as Imp
import qualified Language.Embedded.Imperative.CMD as Imp
import qualified Data.Loc as C
import qualified Language.C.Syntax as C
import qualified Language.C.Quote.C as C

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

instance (Imp.ControlCMD Oper.:<: instr) => Oper.Reexpressible AssertCMD instr env
  where
    reexpressInstrEnv reexp (Assert lbl cond msg) = do
      cond' <- reexp cond
      lift $ Imp.assert cond' msg

--------------------------------------------------------------------------------

data ControlCMD inv fs a
  where
    If :: exp Bool -> prog () -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    While :: Maybe inv -> prog (exp Bool) -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    For :: (pred i, Integral i) =>
      Maybe inv -> Imp.IxRange (exp i) -> Imp.Val i -> prog () ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Break :: ControlCMD inv (Oper.Param3 prog exp pred) ()
    --
    Test :: Maybe (exp Bool) -> String ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Hint :: pred a => exp a ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()
    Comment :: String ->
      ControlCMD inv (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor (ControlCMD inv)
  where
    hfmap f ins = runIdentity (FO.htraverse (pure . f) ins)

instance FO.HTraversable (ControlCMD inv)
  where
    htraverse f (If cond tru fls) = (If cond) <$> f tru <*> f fls
    htraverse f (While inv cond body) = (While inv) <$> f cond <*> f body
    htraverse f (For inv range val body) = (For inv range val) <$> f body
    htraverse _ (Break) = pure Break
    htraverse _ (Test cond msg) = pure (Test cond msg)
    htraverse _ (Hint val) = pure (Hint val)
    htraverse _ (Comment msg) = pure (Comment msg)

--------------------------------------------------------------------------------

data PtrCMD fs a
  where
    SwapPtr :: (pred a, Typeable a, pred i, Typeable i, Ix i, Integral i) =>
      Imp.Arr i a -> Imp.Arr i a -> PtrCMD (Oper.Param3 prog exp pred) ()

instance Oper.HFunctor PtrCMD
  where
    hfmap _ (SwapPtr a b) = SwapPtr a b

instance Oper.HBifunctor PtrCMD
  where
    hbimap _ _ (SwapPtr a b) = SwapPtr a b

instance Oper.InterpBi PtrCMD IO (Oper.Param1 SoftwarePrimType)
  where
    interpBi (SwapPtr (Imp.ArrRun a) (Imp.ArrRun b)) = do
      arr <- readIORef a
      brr <- readIORef b
      writeIORef a brr
      writeIORef b arr

instance (PtrCMD Oper.:<: instr) => Oper.Reexpressible PtrCMD instr env
  where
    reexpressInstrEnv reexp (SwapPtr a b) = do
      lift $ Oper.singleInj (SwapPtr a b)

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
  Oper.:+: PtrCMD
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

class Verifiable prog
  where
    verifyWithResult :: prog a -> V.Verify (prog a, a)

verify :: Verifiable prog => prog a -> V.Verify (prog a)
verify = fmap fst . verifyWithResult

class VerifyInstr instr exp pred
  where
    verifyInstr :: Verifiable prog =>
      instr '(prog, Param2 exp pred) a -> a ->
      V.Verify (instr '(prog, Param2 exp pred) a)
    verifyInstr instr _ = return instr

instance (VerifyInstr f exp pred, VerifyInstr g exp pred) =>
    VerifyInstr (f Imp.:+: g) exp pred
  where
    verifyInstr (Inl m) x = fmap Inl (verifyInstr m x)
    verifyInstr (Inr m) x = fmap Inr (verifyInstr m x)

instance
  ( VerifyInstr (FO.FirstOrder [[SomeLiteral]] prog) exp pred
  , ControlCMD [[SomeLiteral]] Imp.:<: FO.FirstOrder [[SomeLiteral]] prog
  , FO.TypeablePred pred
  , FO.Substitute exp
  , FO.SubstPred exp ~ pred
  , pred Bool
  , FO.Defunctionalise [[SomeLiteral]] prog
  , FO.DryInterp prog)
  =>
    Verifiable (Program prog (Param2 exp pred))
  where
    verifyWithResult prog = do
      let inv = undefined :: [[SomeLiteral]]
      (prog', res) <- verifyWithResult (FO.defunc inv prog)
      return (FO.refunc inv prog', res)

instance
  ( VerifyInstr prog exp pred
  , ControlCMD [[SomeLiteral]] Imp.:<: prog)
  =>
    Verifiable (FO.Sequence prog (Param2 exp pred))
  where
    verifyWithResult (FO.Val x) = return (FO.Val x, x)
    verifyWithResult (FO.Seq x m k) = do
      ((m', breaks), warns) <- V.swallowWarns $ V.getWarns $ V.withBreaks $
        verifyInstr m x
      (_, (k', res)) <- V.ite (breaks) (return ()) (verifyWithResult k)
      let comment msg prog = FO.Seq () (Oper.inj (Comment msg :: ControlCMD [[SomeLiteral]] (Param3 (FO.Sequence prog (Param2 exp pred)) exp pred) ())) prog
      return (foldr comment (FO.Seq x m' k') warns, res)

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

instance (V.SMTEval1 exp, V.SMTEval exp Bool, V.Pred exp ~ pred, pred Bool) =>
    V.VerifyInstr (ControlCMD [[SomeLiteral]]) exp pred
  where
    verifyInstr (Test (Nothing) msg) () =
      return (Test (Nothing) msg)
    verifyInstr (Test (Just cond) msg) () =
      do b   <- V.eval cond
         res <- V.provable "assertion" (V.toSMT b)
         if res then do
           return (Test (Nothing) msg)
         else do
           V.assume "assertion" (V.toSMT b)
           return (Test (Just cond) msg)
    verifyInstr i@(Hint (exp :: exp a)) () =
      withWitness (undefined :: a) i $ 
        do V.eval exp >>= V.hint
    verifyInstr (If cond t f) () =
      do b <- V.eval cond
         (vt, vf) <- V.ite (V.toSMT b) (V.verify t) (V.verify f)
         V.hintFormula (V.toSMT b)
         V.hintFormula (SMT.not (V.toSMT b))
         return (If cond vt vf)
    verifyInstr (While inv cond body) () =
      do let
           loop =
             do b   <- V.verifyWithResult cond
                res <- V.eval (snd b)
                V.ite (V.toSMT res) (V.verify body) V.break
                return ()
         (done, new, _) <- discoverInvariant inv loop
         (vcond, vbody) <- V.stack $
           do (vcond, b) <- V.verifyWithResult cond
              res        <- V.eval b
              V.assume "loop guard" (V.toSMT res)
              vbody      <- V.verify body
              return (vcond, vbody)
         done
         return (While new vcond vbody)
    verifyInstr (For inv range@(lo, step, hi) val@(Imp.ValComp name :: Imp.Val a) body) ()
      | Dict <- V.witnessPred (undefined :: exp a)
      , Dict <- V.witnessNum  (undefined :: exp a)
      , Dict <- V.witnessOrd  (undefined :: exp a) =
      do let
           cond =
             do unsafeFreezeReference name name (undefined :: exp a)
                i <- peekValue name
                n <- V.eval (Imp.borderVal hi)
                m <- V.eval lo
                V.hintFormula (m V..<=. i)
                V.hintFormula (i V..<=. n)
                return (if Imp.borderIncl hi then i V..<=. n else i V..<. n)
         let
           loop body =
             do cond <- cond
                V.ite (SMT.not cond) V.break $
                  do breaks <- V.breaks (V.verify body)
                     V.ite breaks (return ()) $
                       do i <- peekValue name :: V.Verify (V.SMTExpr exp a)
                          setReference name (i + P.fromIntegral step)
                return ()
         old <- S.get
         m   <- V.eval lo
         newReference name (undefined :: exp a)
         setReference name m
         (done, inv, ass) <- discoverInvariant inv (loop body)
         body <- V.noWarn $ V.stack $
           do cond <- cond
              V.assume "loop guard" cond
              V.verify body
         let
           updateCtx :: V.Context ->
                        (forall a. V.Invariant a =>
                          V.Context ->
                          String ->
                          a ->
                          a) ->
                        Verify ()
           updateCtx old f = forM_ (Map.toList old) $
             \(V.Name name _, V.Entry (_ :: b)) ->
               do (x :: b) <- V.peek name
                  V.poke name (f old name x)
         let
           getLits :: (forall a. V.Invariant a =>
                        String ->
                        a ->
                        [(V.Literal a, SMT.SExpr)]) ->
                      V.Verify [SomeLiteral]
           getLits f =
             do new <- S.get
                let cands = [ (SomeLiteral l, e)
                            | (V.Name name _, V.Entry x) <- Map.toList new
                            , (l, e) <- f name x
                            ]
                let ok (SomeLiteral _, e) = V.provable "magic safety invariant" e
                fmap (map fst) (filterM ok cands)
         (lits, lits') <- V.warning ([], []) $ V.stack $
           do -- Iteration 1.
              i :: V.SMTExpr exp a <- getReference name
              updateCtx old (\ctx x -> V.warns1 ctx x . V.warns2 ctx x)
              pre    <- S.get
              breaks <- V.breaks (loop body)
              mid    <- S.get
              lits1  <- getLits V.warnLiterals
              -- Iteration 2.
              V.assume "loop didn't break" (SMT.not breaks)
              ass
              j :: V.SMTExpr exp a <- getReference name
              updateCtx mid V.warns2
              V.assume "distinct iterations" (i V..<. j)
              loop body
              lits2 <- getLits V.warnLiterals
              ctx   <- S.get
              lits' <- getLits $ \name x ->
                map (\x -> (x, V.smtLit pre ctx x)) (V.warnLiterals2 name x)
              return (lits1 `intersect` lits2, lits')
         --
         S.liftIO (putStrLn ("Magic safety literals (body): " ++ show lits))
         S.liftIO (putStrLn ("Magic safety literals (invariant): " ++ show lits'))
         --
         ctx <- S.get
         forM_ lits $ \(SomeLiteral lit) ->
           V.assume "magic safety invariant" (V.smtLit old ctx lit)
         body <- V.stack $
           do forM_ lits $ \(SomeLiteral lit) ->
                V.assume "magic safety invariant" (V.smtLit old ctx lit)
              cond <- cond
              V.assume "loop guard" cond
              V.verify body
         done
         return (For (fmap (++ map return lits') inv) range val body)

--------------------------------------------------------------------------------

-- | The literals used in predicate abstraction.
data SomeLiteral = forall a . V.IsLiteral a => SomeLiteral a

instance Eq SomeLiteral
  where
    x == y = compare x y P.== EQ

instance Show SomeLiteral
  where
    show (SomeLiteral x) = show x

instance Ord SomeLiteral
  where
  compare (SomeLiteral x) (SomeLiteral y) =
    compare (typeOf x) (typeOf y) `mappend`
    case cast y of
      Just y  -> compare x y
      Nothing -> error "weird type error"

-- Takes a loop body, which should break on exit, and does predicate abstraction.
-- Leaves the verifier in a state which represents an arbitrary loop iteration.
-- Returns a value which when run leaves the verifier in a state where the loop
-- has terminated.
discoverInvariant ::
  Maybe [[SomeLiteral]] ->
  V.Verify () ->
  V.Verify (
      V.Verify ()
    , Maybe [[SomeLiteral]]
    , V.Verify ()
    )
discoverInvariant minv body = do
  (frame, hints) <- findFrameAndHints
  (_, _, mode)   <- S.ask
  case minv of
    Nothing | mode P./= V.Execute ->
      do ctx <- S.get
         abs <- abstract ctx frame hints
         refine frame hints abs
    _ ->
      do let
           ass = assumeLiterals frame (fromMaybe [] minv)
           brk = V.noBreak (V.breaks body) >>= V.assume "loop terminated"
         ass >> return (brk, minv, ass)
  where
    -- Suppose we have a while-loop while(E) S, and we know a formula
    -- I(0) which describes the initial state of the loop.
    --
    -- We can describe the state after one iteration by the formula
    --   I(1) := sp(S, I(0) /\ ~E)
    -- where sp(S, P) is the strongest postcondition function.
    -- Likewise, we can describe the state after n+1 iterations by:
    --   I(n+1) := sp(S, I(n) /\ ~E)
    -- The invariant of the loop is then simply
    --   I := I(0) \/ I(1) \/ I(2) \/ ...
    --
    -- Of course, this invariant is infinite and not very useful.
    --
    -- The idea of predicate abstraction is this: if we restrict the
    -- invariant to be a boolean formula built up from a fixed set of
    -- literals, then there are only a finite number of possible
    -- invariants and we can in fact compute an invariant using the
    -- procedure above - at some point I(n+1) = I(n) and then I(n) is
    -- the invariant. We just need to be able to compute the strongest
    -- boolean formula provable in the current verifier state -
    -- something which Abstract.hs provides.
    --
    -- Often a variable is not modified by the loop body, and in that
    -- case we don't need to bother finding an invariant for that
    -- variable - its value is the same as on entry to the loop. We
    -- therefore also compute the set of variables modified by the
    -- loop body, which we call the frame, and only consider literals
    -- that mention frame variables. We do not need to do anything
    -- explicitly for non-frame variables - it is enough to leave them
    -- unchanged in the context when verifying the loop body.
    --
    -- Recall that the goal is to put the verifier in a state
    -- representing an arbitrary loop iteration. Here is how we do
    -- that:
    --   * Find n such that I(n) = I(n+1).
    --   * Havoc the frame variables (update the context to turn them
    --     into fresh SMT variables). This puts the SMT solver in a
    --     state where it knows nothing about those variables, but it
    --     still knows the values of the non-frame variables.
    --   * Assert that I(n) holds.
    --
    -- To find the invariant we must be able to compute I(0),
    -- and to go from I(n) to I(n+1). To compute I(0), we just run
    -- predicate abstraction in the state we initially find ourselves
    -- in. To get from I(n) to I(n+1) we do the following:
    --   * Havoc the frame variables and then assert I(n). Similar to
    --     above, this tells the verifier that we are in an arbitrary
    --     state in which I(n) holds.
    --   * Assert that the loop has not terminated yet, execute the
    --     loop body once, and use predicate abstraction to compute a
    --     new formula P describing the state we are in now.
    --     This corresponds to sp(S, I(n) /\ ~E). Then let
    --     I(n+1) = I(n) \/ P.
    -- Note that we do all this inside a call to "stack" so that
    -- it doesn't permanently change the verifier state.
    findFrameAndHints = V.stack $ V.quietly $ V.noWarn $ V.quickly $ do
      -- Put the verifier in an arbitrary state.
      ctx <- S.get
      let
        op ctx (V.Name name _, V.Entry (x :: a)) = do
          val <- V.havoc name x
          return (V.insertContext name (val :: a) ctx)
      before <- foldM op Map.empty (Map.toList ctx)
      S.put before

      -- Run the program and see what changed.
      (_, _, hints, decls) <- fmap snd (S.listen body)
      after <- S.get

      let
        atoms (SMT.Atom x) = [x]
        atoms (SMT.List xs) = concatMap atoms xs

        hints' =
          [ V.Hint before hint
          | hint <- nub hints,
            null (intersect decls (atoms (V.hb_exp hint))) ]

      return (Map.toList (V.modified before after), hints')

    refine frame hints clauses = do
      ctx <- S.get
      clauses' <- V.stack $ V.quietly $ V.noWarn $ do
        assumeLiterals frame clauses
        V.noBreak (V.breaks body) >>= V.assume "loop not terminated" . SMT.not
        fmap (disjunction clauses) (V.chattily (abstract ctx frame hints))

      if clauses P.== clauses' then do
        printInvariant "Invariant" frame clauses
        let ass = assumeLiterals frame clauses
        ass
        return (V.noBreak (V.breaks body) >>= V.assume "loop terminated", Just clauses, ass)
      else refine frame hints clauses'

    assumeLiterals :: [(V.Name, V.Entry)] -> [[SomeLiteral]] -> Verify ()
    assumeLiterals frame clauses = do
      ctx <- S.get
      forM_ frame $ \(V.Name name _, V.Entry (_ :: a)) -> do
        val <- V.peek name >>= V.havoc name
        V.poke name (val :: a)
      mapM_ (\clause -> (evalClause ctx >=> V.assume (show clause)) clause) clauses

    abstract old frame hints = fmap (usort . map usort) $ do
      res <- V.quietly $ fmap concat $ mapM (A.abstract (\clause -> (evalClause old >=> V.provable (show clause)) clause)) (lits frame)
      printInvariant "Candidate invariant" frame res
      return res
      where
        lits frame =
          partitionBy (\(SomeLiteral x) -> V.phase x) $
          concat [ map SomeLiteral (V.literals name x) | (V.Name name _, V.Entry x) <- frame ] ++
          [ SomeLiteral hint | hint <- hints, V.hb_type (V.hint_body hint) P.== SMT.tBool ]

    printInvariant kind frame [] =
      S.liftIO $
        putStrLn ("No invariant found over frame " ++ show (map fst frame))
    printInvariant kind frame clauses = S.liftIO $ do
      putStrLn (kind ++ " over frame " ++ show (map fst frame) ++ ":")
      sequence_ [ putStrLn ("  " ++ show clause) | clause <- clauses ]

    disjunction cs1 cs2 = prune (usort [ usort (c1 ++ c2) | c1 <- cs1, c2 <- cs2 ])
      where
        prune cs = [ c | c <- cs, and [ c P.== c' P.|| c' \\ c P./= [] | c' <- cs ] ]

    usort :: Ord a => [a] -> [a]
    usort = map head . group . sort

    partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
    partitionBy f xs = groupBy ((P.==) `on` f) (sortBy (comparing f) xs)

evalClause :: V.Context -> [SomeLiteral] -> V.Verify SMT.SExpr
evalClause old clause = do
  ctx <- S.get
  return (SMT.disj [ V.smtLit old ctx lit | SomeLiteral lit <- clause ])

--------------------------------------------------------------------------------

-- reveal :: Typeable a => Variable -> a
-- reveal (Variable a _) = fromMaybe (error "substitution type error") (cast a)

type instance FO.Id (Imp.Ref a)    = C.Id
type instance FO.Id (Imp.Val a)    = C.Id
type instance FO.Id (Imp.Arr  i a) = C.Id
type instance FO.Id (Imp.IArr i a) = C.Id
type instance FO.Id (Imp.Handle)   = C.Id

instance (Typeable a) => FO.Variable (Imp.Ref a)
  where
    hide a = FO.Hidden a (C.toIdent a C.noLoc)

instance (Typeable a) => FO.Variable (Imp.Val a)
  where
    hide a = FO.Hidden a (C.toIdent a C.noLoc)

instance (Typeable a, Typeable i) => FO.Variable (Imp.Arr i a)
  where
    hide a = FO.Hidden a (C.toIdent a C.noLoc)

instance (Typeable a, Typeable i) => FO.Variable (Imp.IArr i a)
  where
    hide a = FO.Hidden a (C.toIdent a C.noLoc)

instance FO.Variable (Imp.Handle)
  where
    hide a = FO.Hidden a (C.toIdent a C.noLoc)

witnessVal :: forall f i j e pred a b . (FO.TypeablePred pred, Typeable f)
  => f a
  -> (Typeable a => FO.Recovered i j e pred b)
  -> (pred a     => FO.Recovered i j e pred b)
witnessVal _ x = case FO.witnessTypeable (Dict :: Dict (pred a)) of Dict -> x

witnessArr :: forall f i j e pred a b c . (FO.TypeablePred pred, Typeable f)
  => f a b
  -> (Typeable a => Typeable b => FO.Recovered i j e pred c)
  -> (pred a     => pred b     => FO.Recovered i j e pred c)
witnessArr f x = case FO.witnessTypeable (Dict :: Dict (pred a)) of Dict -> witnessVal f x

witness1 :: forall f i j e pred a . (FO.TypeablePred pred, Typeable f)
  => (Typeable a => FO.Recovered i j e pred (f a))
  -> (pred a     => FO.Recovered i j e pred (f a))
witness1 = witnessVal (undefined :: f a)

witness2 :: forall f i j e pred a b . (FO.TypeablePred pred, Typeable f)
  => (Typeable a => Typeable b => FO.Recovered i j e pred (f a b))
  -> (pred a     => pred b     => FO.Recovered i j e pred (f a b))
witness2 = witnessArr (undefined :: f a b)

instance FO.Defunctionalise inv Imp.RefCMD
  where
    refunctionalise _ sub (Imp.NewRef name) =
      witness1 (FO.Keep (Imp.NewRef name))
    refunctionalise _ sub (Imp.InitRef name exp) =
      witness1 (FO.Keep (Imp.InitRef name (FO.subst sub exp)))
    refunctionalise _ sub (Imp.GetRef ref) =
      witnessVal ref (FO.Keep (Imp.GetRef (FO.lookupSubst sub ref)))
    refunctionalise _ sub (Imp.SetRef ref exp) =
      witnessVal ref (FO.Discard (Imp.SetRef
        (FO.lookupSubst sub ref) (FO.subst sub exp)))
    refunctionalise _ sub (Imp.UnsafeFreezeRef ref) =
      witnessVal ref (FO.Keep (Imp.UnsafeFreezeRef (FO.lookupSubst sub ref)))

instance FO.Defunctionalise inv Imp.ArrCMD
  where
    refunctionalise _ sub (Imp.NewArr name n) =
      witness2 (FO.Keep (Imp.NewArr name (FO.subst sub n)))
    refunctionalise _ sub (Imp.ConstArr name xs) =
      witness2 (FO.Keep (Imp.ConstArr name xs))
    refunctionalise _ sub (Imp.GetArr arr i) =
      witnessArr arr (FO.Keep (Imp.GetArr
        (FO.lookupSubst sub arr) (FO.subst sub i)))
    refunctionalise _ sub (Imp.SetArr arr i exp) =
      witnessArr arr (FO.Discard (Imp.SetArr
        (FO.lookupSubst sub arr) (FO.subst sub i) (FO.subst sub exp)))
    refunctionalise _ sub (Imp.CopyArr (arr, i) (brr, j) n) =
      witnessArr arr (FO.Discard (Imp.CopyArr
        (FO.lookupSubst sub arr, FO.subst sub i)
        (FO.lookupSubst sub brr, FO.subst sub j)
        (FO.subst sub n)))
    refunctionalise _ sub (Imp.UnsafeFreezeArr arr) =
      witness2 (FO.Keep (Imp.UnsafeFreezeArr (FO.lookupSubst sub arr)))
    refunctionalise _ sub (Imp.UnsafeThawArr iarr) =
      witness2 (FO.Keep (Imp.UnsafeThawArr (FO.lookupSubst sub iarr)))

instance FO.Defunctionalise inv Imp.FileCMD
  where
    refunctionalise _ sub (Imp.FOpen name mode) =
      FO.Keep (Imp.FOpen name mode)
    refunctionalise _ sub (Imp.FClose h) =
      FO.Discard (Imp.FClose (FO.lookupSubst sub h))
    refunctionalise _ sub (Imp.FEof h) =
      FO.Keep (Imp.FEof (FO.lookupSubst sub h))
    refunctionalise _ sub (Imp.FPrintf h msg args) =
      FO.Discard (Imp.FPrintf (FO.lookupSubst sub h) msg
        (map (Imp.mapPrintfArg (FO.subst sub)) args))
    refunctionalise _ sub (Imp.FGet h) =
      witness1 (FO.Keep (Imp.FGet (FO.lookupSubst sub h)))

instance FO.Defunctionalise inv Imp.ControlCMD
  where
    type FirstOrder inv Imp.ControlCMD = ControlCMD inv

    defunctionalise _ (Imp.If cond t f) =
      return (If cond t f)
    defunctionalise _ (Imp.While cond body) =
      return (While Nothing cond body)
    defunctionalise _ (Imp.For range body) = do
      ix <- fmap (Imp.ValComp . ('v':) . show) FO.fresh
      return (For Nothing range ix (body ix))
    defunctionalise _ (Imp.Break) =
      return Break
    defunctionalise _ (Imp.Assert cond msg) =
      return (Test (Just cond) msg)
    defunctionalise _ (Imp.Hint exp) =
      return (Hint exp)

    refunctionalise inv sub (If cond t f) =
      FO.Discard (Imp.If (FO.subst sub cond)
        (FO.refuncM inv sub t)
        (FO.refuncM inv sub f))
    refunctionalise inv sub (While _ cond body) =
      FO.Discard (Imp.While
        (FO.refuncM inv sub cond)
        (FO.refuncM inv sub body))
    refunctionalise inv sub (For _ (lo :: exp i, step, hi) ix body) =
      witnessVal ix $ FO.Discard $ Imp.For
        (FO.subst sub lo, step, fmap (FO.subst sub) hi)
        (\jx -> FO.refuncM inv (FO.extendSubst ix jx sub) body)
    refunctionalise inv sub (Break) =
      FO.Discard Imp.Break
    refunctionalise inv sub (Test (Just cond) msg) =
      FO.Discard (Imp.Assert (FO.subst sub cond) msg)
    refunctionalise inv sub (Hint exp) =
      FO.Discard (Imp.Hint (FO.subst sub exp))

instance FO.HTraversable Imp.RefCMD
instance FO.HTraversable Imp.ArrCMD
instance FO.HTraversable Imp.FileCMD

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
