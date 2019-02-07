{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language DataKinds #-}
{-# language ScopedTypeVariables #-}
{-# language TypeFamilies #-}
{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language PolyKinds #-}
{-# language GeneralizedNewtypeDeriving #-}

module Feldspar.Verify.Monad where

import Control.Monad.RWS.Strict
import Control.Monad.Exception
import Control.Monad.Operational.Higher (Program)

import Data.List hiding (break)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Ord
import Data.Function
import Data.Typeable
import Data.Constraint (Constraint, Dict(..))
import Data.Maybe
import Data.Array
import Data.ALaCarte

import Control.Monad.FirstOrder hiding (fresh)
import Feldspar.Verify.SMT hiding (not, ite, stack, concat)
import qualified Control.Monad.FirstOrder as FO
import qualified Feldspar.Verify.SMT as SMT
import qualified Feldspar.Verify.Abstract as Abstract

import Prelude hiding (break)

--------------------------------------------------------------------------------
-- * Verification monad.
--------------------------------------------------------------------------------
-- Based on https://github.com/nick8325/imperative-edsl/blob/master/src/Language/Embedded/Verify.hs
--
-- Our verification algorithm looks a lot like symbolic execution. The
-- difference is that we use an SMT solver to do the symbolic reasoning.
--
-- We model the state of the program as the state of the SMT solver plus a
-- context, which is a map from variable name to SMT value. Symbolically
-- executing a statement modifies this state to become the state after executing
-- the statement. Typically, this modifies the context (when a variable has
-- changed) or adds new axioms to the SMT solver.
--
-- The verification monad allows us to easily manipulate the SMT solver and the
-- context. It also provides three other features:
--
-- First, it supports branching on the value of a formula, executing one branch
-- if the formula is true and the other if the formula is false. The monad takes
-- care of merging the contexts from the two branches afterwards, as well as
-- making sure that any axiom we add inside a branch is only assumed
-- conditionally.
--
-- Second, it supports break statements in a rudimentary way. We can record when
-- we reach a break statement, and ask the monad for a symbolic expression that
-- tells us whether a given statement breaks. However, skipping past statements
-- after a break is the responsibility of the user of the monad.
--
-- Finally, we can emit warnings during verification, for example when we detect
-- a read of an uninitialised reference.
--
--------------------------------------------------------------------------------

-- | The Verify monad itself is a reader/writer/state monad with the following
-- components:
--
-- Read:  list of formulas which are true in the current branch;
--        "chattiness level" (if > 0 then tracing messages are printed);
--        whether to try to prove anything or just evaluate the program.
--
-- Write: disjunction which is true if the program has called break;
--        list of warnings generated;
--        list of hints given;
--        list of names generated (must not appear in hints).
--
-- State: the context, a map from variables to SMT values.
--
type Verify = RWST ([SExpr], Int, Mode) ([SExpr], Warns, [HintBody], [String]) Context SMT

-- | The verification monad can prove (with and without warnings) or simply
-- execute a computation.
data Mode = Prove | ProveAndWarn | Execute deriving Eq

-- | Warkings are either local warnings for a branch or global.
data Warns = Warns {
    warns_here :: [String]
  , warns_all  :: [String] }

instance Monoid Warns
  where
    mempty = Warns [] []
    w1 `mappend` w2 = Warns
      (warns_here w1 `mappend` warns_here w2)
      (warns_all w1 `mappend` warns_all w2)

--------------------------------------------------------------------------------

-- | Run and prove a computation and record all warnings.
runVerify :: Verify a -> IO (a, [String])
runVerify m = runZ3 [] $ do
  SMT.setOption ":produce-models" "false"
  (x, (_, warns, _, _)) <- evalRWST m ([], 0, ProveAndWarn) Map.empty
  return (x, warns_all warns)

-- | Run a computation without proving anything.
quickly :: Verify a -> Verify a
quickly = local (\(branch, chat, _) -> (branch, chat, Execute))

-- | Only run a computation if we are supposed to be proving.
proving :: a -> Verify a -> Verify a
proving def mx = do
  (_, _, mode) <- ask
  case mode of
    Prove        -> mx
    ProveAndWarn -> mx
    Execute      -> return def

-- | Only run a computation if we are supposed to be warning.
warning :: a -> Verify a -> Verify a
warning x mx = do
  (_, _, mode) <- ask
  if (mode == ProveAndWarn) then mx else return x

--------------------------------------------------------------------------------

-- | Assume that a given formula is true.
assume :: String -> SExpr -> Verify ()
assume msg p = proving () $ do
  branch <- branch
  trace msg "Asserted" p
  lift (assert (disj (p:map SMT.not branch)))

-- | Check if a given formula holds.
provable :: String -> SExpr -> Verify Bool
provable msg p = proving False $ do
  branch <- branch
  stack $ do
    res <- lift $ do
      mapM_ assert branch
      assert (SMT.not p)
      check
    chat $
      case res of
        Sat -> stack $ do
          trace msg "Failed to prove" p
          lift $ setOption ":produce-models" "true"
          lift $ check
          context <- get
          model   <- showModel context
          liftIO $ putStrLn (" (countermodel is " ++ model ++ ")")
        Unsat   -> trace msg "Proved" p
        Unknown -> trace msg "Couldn't solve" p
    return (res == Unsat)

-- | Run a computation but undo its effects afterwards.
stack :: Verify a -> Verify a
stack mx = do
  state <- get
  read  <- ask
  fmap fst $ lift $ SMT.stack $ evalRWST mx read state

-- | Branch on the value of a formula.
ite :: SExpr -> Verify a -> Verify b -> Verify (a, b)
ite p mx my = do
  ctx  <- get
  read <- ask
  let
    withBranch p
      | p == bool True  = local id
      | p == bool False = local (\(_,  x, y) -> ([p],  x, y))
      | otherwise       = local (\(xs, x, y) -> (p:xs, x, y))
  (x, ctx1, (break1, warns1, hints1, decls1)) <- lift $ runRWST (withBranch p mx) read ctx
  (y, ctx2, (break2, warns2, hints2, decls2)) <- lift $ runRWST (withBranch (SMT.not p) my) read ctx
  mergeContext p ctx1 ctx2 >>= put
  let
    break
      | null break1 && null break2 = []
      | otherwise = [SMT.ite p (disj break1) (disj break2)]
  tell (break, warns1 `mappend` warns2, hints1 ++ hints2, decls1 ++ decls2)
  return (x, y)

--------------------------------------------------------------------------------

-- | Read the current branch.
branch :: Verify [SExpr]
branch = asks (\(branch, _, _) -> branch)

-- | Read the context.
peek :: (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> Verify a
peek name = do
  ctx <- get
  return (lookupContext name ctx)

-- | Write to the context.
poke :: (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> a -> Verify ()
poke name val = modify (insertContext name val)

-- | Record that execution has broken here.
break :: Verify ()
break = do
  branch <- branch
  tell ([conj branch], mempty, [], [])

-- | Check if execution of a statement can break.
withBreaks :: Verify a -> Verify (a, SExpr)
withBreaks mx = do
  (x, (exits, _, _, _)) <- listen mx
  return (x, disj exits)

-- | Check if execution of a statement can break, discarding the statement's
--   result.
breaks :: Verify a -> Verify SExpr
breaks mx = fmap snd (withBreaks mx)

-- | Prevent a statement from breaking.
noBreak :: Verify a -> Verify a
noBreak = censor (\(_, warns, hints, decls) -> ([], warns, hints, decls))

-- | Add a warning to the output.
warn :: String -> Verify ()
warn msg = warning () $ tell ([], Warns [msg] [msg], [], [])

-- | Add a hint to the output.
hint :: TypedSExpr a => a -> Verify ()
hint exp = tell ([], mempty, [HintBody (toSMT exp) (smtType exp)], [])

-- | Add a hint for a formula to the output.
-- hintFormula :: SExpr -> Verify ()
-- hintFormula exp = tell ([], mempty, [HintBody exp tBool],[])

-- | Run a computation but ignoring its warnings.
noWarn :: Verify a -> Verify a
noWarn = local (\(x, y, mode) -> (x, y, f mode))
  where
    f ProveAndWarn = Prove
    f x = x

-- | Run a computation but ignoring its local warnings.
-- swallowWarns :: Verify a -> Verify a
-- swallowWarns = censor (\(x, ws, y, z) -> (x, ws { warns_here = [] }, y, z))

-- | Run a computation and get its warnings.
getWarns :: Verify a -> Verify (a, [String])
getWarns mx = do
  (x, (_, warns, _, _)) <- listen mx
  return (x, warns_here warns)

--------------------------------------------------------------------------------
-- ** The API for verifying programs.
--------------------------------------------------------------------------------

-- | A typeclass for things which can be symbolically executed.
class Verifiable prog
  where
    -- Returns the transformed program (in which e.g. proved assertions
    -- may have been removed), together with the result.
    verifyWithResult :: prog a -> Verify (prog a, a)

-- | Symbolically execute a program, ignoring the result.
verify :: Verifiable prog => prog a -> Verify (prog a)
verify = fmap fst . verifyWithResult

--------------------------------------------------------------------------------

-- | A typeclass for instructions which can be symbolically executed.
class VerifyInstr instr exp pred
  where
    verifyInstr :: Verifiable prog => instr '(prog, Param2 exp pred) a -> a -> Verify (instr '(prog, Param2 exp pred) a)
    verifyInstr instr _ = return instr

instance (VerifyInstr f exp pred, VerifyInstr g exp pred) => VerifyInstr (f :+: g) exp pred
  where
    verifyInstr (Inl m) x = fmap Inl (verifyInstr m x)
    verifyInstr (Inr m) x = fmap Inr (verifyInstr m x)

--------------------------------------------------------------------------------
-- ** Expressions and invariants.
--------------------------------------------------------------------------------

-- | A typeclass for expressions which can be evaluated under a context.
class Typeable exp => SMTEval1 exp
  where
    -- The result type of evaluating the expression.
    data SMTExpr exp a
    -- A predicate which must be true of the expression type.
    type Pred exp :: * -> Constraint
    -- Evaluate an expression to its SMT expression.
    eval :: exp a -> Verify (SMTExpr exp a)
    -- Witness the fact that (SMTEval1 exp, Pred exp a) => SMTEval exp a.
    witnessPred :: Pred exp a => exp a -> Dict (SMTEval exp a)

--------------------------------------------------------------------------------

-- | A typeclass for expressions of a particular type.
class (SMTEval1 exp, TypedSExpr (SMTExpr exp a), Typeable a) => SMTEval exp a
  where
    -- Lift a typed constant into a SMT expression.
    fromConstant :: a -> SMTExpr exp a
    -- Witness the numerical type of an expression.
    witnessNum :: Num a => exp a -> Dict (Num (SMTExpr exp a))
    witnessNum = error "witnessNum"
    -- Witness the ordered type of an expression.
    witnessOrd :: Ord a => exp a -> Dict (SMTOrd (SMTExpr exp a))
    witnessOrd = error "witnessOrd"
    -- Produce an index for a type.
    skolemIndex :: Ix a => SMTExpr exp a
    skolemIndex = error "skolemIndex"

--------------------------------------------------------------------------------

-- | A typeclass for values with a representation as an SMT expression. 
class Fresh a => TypedSExpr a
  where
    smtType :: a -> SExpr
    toSMT   :: a -> SExpr
    fromSMT :: SExpr -> a

-- | Spawn a new expression, the string is a hint for making a pretty name.
freshSExpr :: forall a. TypedSExpr a => String -> Verify a
freshSExpr name = fmap fromSMT (freshVar name (smtType (undefined :: a)))

--------------------------------------------------------------------------------

-- | A typeclass for values that support uninitialised creation.
class Fresh a
  where
    -- Create an uninitialised value. The String argument is a hint for making
    -- pretty names.
    fresh :: String -> Verify a

-- | Create a fresh variable and initialize it.
freshVar :: String -> SExpr -> Verify SExpr
freshVar name ty = do
  n <- lift freshNum
  let x = name ++ "." ++ show n
  tell ([], mempty, [], [x])
  lift $ declare x ty

--------------------------------------------------------------------------------

-- | A typeclass for values that can undergo predicate abstraction.
class (IsLiteral (Literal a), Fresh a) => Invariant a
  where
    data Literal a

    -- Forget the value of a binding.
    havoc :: String -> a -> Verify a
    havoc name _ = fresh name

    -- Return a list of candidate literals for a value.
    literals :: String -> a -> [Literal a]
    literals _ _ = []

    warns1, warns2 :: Context -> String -> a -> a
    warns1 _ _ x = x
    warns2 _ _ x = x

    warnLiterals :: String -> a -> [(Literal a, SExpr)]
    warnLiterals _ _ = []

    warnLiterals2 :: String -> a -> [Literal a]
    warnLiterals2 _ _ = []

--------------------------------------------------------------------------------

class (Ord a, Typeable a, Show a) => IsLiteral a
  where
    -- Evaluate a literal. The two context arguments are the old and new
    -- contexts (on entry to the loop and now).
  smtLit :: Context -> Context -> a -> SExpr
  smtLit = error "smtLit not defined"

  -- What phase is the literal in? Literals from different phases cannot be
  -- combined in one clause.
  phase :: a -> Int
  phase _ = 0

--------------------------------------------------------------------------------

data HintBody = HintBody {
    hb_exp  :: SExpr
  , hb_type :: SExpr }
  deriving (Eq, Ord)

instance Show HintBody
  where
    show = showSExpr . hb_exp

data Hint = Hint {
    hint_ctx  :: Context
  , hint_body :: HintBody }
  deriving (Eq, Ord)

instance Show Hint
  where
    show = show . hint_body

instance IsLiteral Hint
  where
    smtLit _ ctx hint = subst (hb_exp (hint_body hint))
      where
        subst x | Just y <- lookup x sub = y
        subst (Atom xs) = Atom xs
        subst (List xs) = List (map subst xs)

        sub = equalise (hint_ctx hint) ctx

        equalise ctx1 ctx2 = zip (exprs (fmap fst m)) (exprs (fmap snd m))
          where
            m = Map.intersectionWith (,) ctx1 ctx2

--------------------------------------------------------------------------------

-- | A typeclass for values that contain SMT expressions.
class Exprs a
  where
    -- List SMT expressions contained inside a value.
    exprs :: a -> [SExpr]

instance Exprs SExpr
  where
    exprs x = [x]

instance Exprs Entry
  where
    exprs (Entry x) = exprs x

instance Exprs Context
  where
    exprs = concatMap exprs . Map.elems

----------------------------------------------------------------------
-- ** The context.
----------------------------------------------------------------------

data Name  = forall a. Typeable a => Name String a

instance Eq Name
  where
    x == y = compare x y == EQ

instance Ord Name
  where
    compare = comparing (\(Name name x) -> (name, typeOf x))

instance Show Name
  where
    show (Name name _) = name

data Entry = forall a. (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => Entry a

instance Eq Entry
  where
    Entry x == Entry y = typeOf x == typeOf y && cast x == Just y

instance Ord Entry
  where
    compare (Entry x) (Entry y) = compare (typeOf x) (typeOf y) `mappend` compare (Just x) (cast y)
    
instance Show Entry
  where
    showsPrec n (Entry x) = showsPrec n x

type Context = Map Name Entry

-- Look up a value in the context.
lookupContext :: forall a . Typeable a => String -> Context -> a
lookupContext name ctx =
  case maybeLookupContext name ctx of
    Nothing -> error ("variable " ++ name ++ " not found in context")
    Just x -> x

maybeLookupContext :: forall a . Typeable a => String -> Context -> Maybe a
maybeLookupContext name ctx = do
  Entry x <- Map.lookup (Name name (undefined :: a)) ctx
  case cast x of
    Nothing -> error "type mismatch in lookup"
    Just x  -> return x

-- Add a value to the context or modify an existing binding.
insertContext :: forall a . (Typeable a, Ord a, Mergeable a, Show a, ShowModel a, Invariant a, Exprs a) => String -> a -> Context -> Context
insertContext name x ctx = Map.insert (Name name (undefined :: a)) (Entry x) ctx

-- modified ctx1 ctx2 returns a subset of ctx2 that contains
-- only the values that have been changed from ctx1.
modified :: Context -> Context -> Context
modified ctx1 ctx2 = Map.mergeWithKey f (const Map.empty) (const Map.empty) ctx1 ctx2
  where
    f _ x y
      | x == y    = Nothing
      | otherwise = Just y

--------------------------------------------------------------------------------

-- | A typeclass for values that support if-then-else.
class Mergeable a
  where
    merge :: SExpr -> a -> a -> a

mergeContext :: SExpr -> Context -> Context -> Verify Context
mergeContext cond ctx1 ctx2 =
  -- If a variable is bound conditionally, put it in the result
  -- context, but only define it conditionally.
  sequence $
    Map.mergeWithKey
      (const combine)
      (fmap (definedWhen cond))
      (fmap (definedWhen (SMT.not cond)))
      ctx1 ctx2
  where
    combine :: Entry -> Entry -> Maybe (Verify Entry)
    combine x y = Just (return (merge cond x y))

    definedWhen :: SExpr -> Entry -> Verify Entry
    definedWhen cond (Entry x) = do
      y <- fresh "unbound"
      return (Entry (merge cond x y))

instance Mergeable Entry
  where
    merge cond (Entry x) (Entry y) = case cast y of
      Just y  -> Entry (merge cond x y)
      Nothing -> error "incompatible types in merge"

instance Mergeable SExpr
  where
    merge cond t e
      | t == e = t
      | cond == bool True  = t
      | cond == bool False = e
      | otherwise = SMT.ite cond t e

--------------------------------------------------------------------------------

-- | A typeclass for values that can be shown given a model from the SMT solver.
class ShowModel a
  where
    showModel :: a -> Verify String

instance ShowModel Context
  where
    showModel ctx = do
      let (keys, values) = unzip (Map.toList ctx)
      values' <- mapM showModel values
      return (intercalate ", " (zipWith (\(Name k _) v -> k ++ " = " ++ v) keys values'))

instance ShowModel Entry
  where
    showModel (Entry x) = showModel x

instance ShowModel SExpr
  where
    showModel x = lift (getExpr x) >>= return . showValue

--------------------------------------------------------------------------------
-- ** The different bindings that are stored in the context.
--------------------------------------------------------------------------------

-- | A normal variable binding.
data ValBinding exp a = ValBinding {
    vb_value :: SMTExpr exp a
  , vb_ref   :: Maybe String }
  deriving (Eq, Ord, Show, Typeable)

instance SMTEval exp a => Mergeable (ValBinding exp a)
  where
    merge cond x y = case (vb_ref x, vb_ref y) of
      (Just r1, Just r2) | r1 /= r2 -> error "immutable binding bound in two locations"
      _ -> ValBinding {
          vb_value = merge cond (vb_value x) (vb_value y)
        , vb_ref   = vb_ref x `mplus` vb_ref y }

instance SMTEval exp a => ShowModel (ValBinding exp a)
  where
    showModel = showModel . vb_value

instance SMTEval exp a => Fresh (ValBinding exp a)
  where
    fresh name = do
      val <- fresh name
      return (ValBinding val Nothing)

instance SMTEval exp a => Invariant (ValBinding exp a)
  where
    data Literal (ValBinding exp a) = LitVB deriving (Eq, Ord, Show, Typeable)

instance SMTEval exp a => IsLiteral (Literal (ValBinding exp a))

instance SMTEval exp a => Exprs (ValBinding exp a)
  where
    exprs val = [toSMT (vb_value val)]

peekVal :: forall exp a. SMTEval exp a => String -> Verify (SMTExpr exp a)
peekVal name = do
  ValBinding val ref <- peek name
  warning () $
    case ref of
      Nothing -> return ()
      Just refName -> do
        ref <- peek refName :: Verify (RefBinding exp a)
        safe <- provable "reference not frozen" (val .==. rb_value ref)
        unless safe (warn ("Unsafe use of frozen reference " ++ name))
  return val

pokeVal :: SMTEval exp a => String -> SMTExpr exp a -> Verify ()
pokeVal name val = poke name (ValBinding val Nothing)

--------------------------------------------------------------------------------

-- | A binding for a reference.
data RefBinding exp a = RefBinding {
    rb_value       :: SMTExpr exp a
  , rb_initialised :: SExpr }
  deriving (Eq, Ord, Show, Typeable)

instance SMTEval exp a => Mergeable (RefBinding exp a)
  where
    merge cond (RefBinding v1 i1) (RefBinding v2 i2) = RefBinding (merge cond v1 v2) (merge cond i1 i2)

instance SMTEval exp a => ShowModel (RefBinding exp a)
  where
    showModel = showModel . rb_value

instance SMTEval exp a => Fresh (RefBinding exp a)
  where
    fresh name = do
      value <- fresh name
      init  <- freshVar (name ++ ".init") tBool
      return (RefBinding value init)

instance SMTEval exp a => Invariant (RefBinding exp a)
  where
    data Literal (RefBinding exp a) =
        RefInitialised String
      | RefUnchanged String
      deriving (Eq, Ord, Show, Typeable)

    literals name _ = [RefInitialised name, RefUnchanged name]

instance SMTEval exp a => IsLiteral (Literal (RefBinding exp a))
  where
    smtLit _ ctx (RefInitialised name) = rb_initialised (lookupContext name ctx :: RefBinding exp a)
    smtLit old new (RefUnchanged name) = toSMT (rb_value x) `eq` toSMT (rb_value y)
      where
        x, y :: RefBinding exp a
        x = lookupContext name old
        y = lookupContext name new

instance SMTEval exp a => Exprs (RefBinding exp a)
  where
    exprs ref = [toSMT (rb_value ref), rb_initialised ref]

newRef :: SMTEval exp a => String -> exp a -> Verify ()
newRef name (_ :: exp a) = do
  ref <- fresh name
  poke name (ref { rb_initialised = bool False } :: RefBinding exp a)

getRef :: SMTEval exp a => String -> Verify (SMTExpr exp a)
getRef name = do
  ref <- peek name
  warning () $ do
    safe <- provable "reference initialised" (rb_initialised ref)
    unless safe (warn (name ++ " read before initialisation"))
  return (rb_value ref)

setRef :: forall exp a. SMTEval exp a => String -> SMTExpr exp a -> Verify ()
setRef name val = do
  ref <- peek name :: Verify (RefBinding exp a)
  poke name ref{rb_value = val, rb_initialised = bool True}

unsafeFreezeRef :: forall exp a. SMTEval exp a => String -> String -> exp a -> Verify ()
unsafeFreezeRef refName valName (_ :: exp a) = do
  ref <- peek refName :: Verify (RefBinding exp a)
  poke valName (ValBinding (rb_value ref) (Just refName))

--------------------------------------------------------------------------------

-- | A binding that represents the contents of an array.
data ArrContents exp i a = ArrContents {
    ac_value :: SMTArray exp i a
  , ac_bound :: SMTExpr exp i }
  deriving (Eq, Ord, Typeable, Show)

instance (SMTEval exp a, SMTEval exp i) => Mergeable (ArrContents exp i a)
  where
    merge cond (ArrContents v1 b1) (ArrContents v2 b2) = ArrContents (merge cond v1 v2) (merge cond b1 b2)

instance (SMTEval exp a, SMTEval exp i) => ShowModel (ArrContents exp i a)
  where
    showModel arr = lift $ do
      bound <- getExpr (toSMT (ac_bound arr))
      showArray bound (toSMT (ac_value arr))

instance (SMTEval exp a, SMTEval exp i) => Fresh (ArrContents exp i a)
  where
    fresh name = do
      value <- fresh (name ++ ".value")
      bound <- fresh (name ++ ".bound")
      return (ArrContents value bound)

instance (SMTEval exp a, SMTEval exp i) => Invariant (ArrContents exp i a)
  where
    data Literal (ArrContents exp i a) = LitAC deriving (Eq, Ord, Show, Typeable)

    havoc name arr = do
      value <- fresh name
      return ArrContents { ac_value = value, ac_bound = ac_bound arr }

instance (SMTEval exp a, SMTEval exp i) => IsLiteral (Literal (ArrContents exp i a))

instance (SMTEval exp a, SMTEval exp i) => Exprs (ArrContents exp i a)
  where
    exprs arr = [toSMT (ac_bound arr), toSMT (ac_value arr)]

--------------------------------------------------------------------------------

-- | A binding that represents a reference to an array.
data ArrBinding exp i a = ArrBinding {
    arr_source     :: Maybe String
  , arr_accessible :: SExpr
  , arr_readable   :: SExpr
  , arr_failed     :: SExpr }
  deriving (Eq, Ord, Typeable, Show)

instance (SMTEval exp a, SMTEval exp i) => Mergeable (ArrBinding exp i a)
  where
    merge cond (ArrBinding s1 a1 r1 f1) (ArrBinding s2 a2 r2 f2) = ArrBinding (s1 `mplus` s2) (merge cond a1 a2) (merge cond r1 r2) (merge cond f1 f2)

instance (SMTEval exp a, SMTEval exp i) => ShowModel (ArrBinding exp i a)
  where
    showModel ArrBinding{arr_source = Nothing}     = return "<unbound array>"
    showModel ArrBinding{arr_source = Just source} = do
      src <- peek source
      showModel (src :: ArrContents exp i a)

instance (SMTEval exp a, SMTEval exp i) => Exprs (ArrBinding exp i a)
  where
    exprs (ArrBinding _ a r f) = [a, r, f]

instance (SMTEval exp a, SMTEval exp i) => Fresh (ArrBinding exp i a)
  where
    fresh name = do
      accessible <- freshVar (name ++ ".ok") tBool
      readable <- freshVar (name ++ ".read") tBool
      failed <- freshVar (name ++ ".failed") tBool
      return (ArrBinding Nothing accessible readable failed)

instance (SMTEval exp a, SMTEval exp i) => Invariant (ArrBinding exp i a)
  where
    data Literal (ArrBinding exp i a) =
        ArrAccessible String
      | ArrReadable String
      | ArrSafetyPreserved String
      deriving (Eq, Ord, Show, Typeable)

    literals name _ = [ArrAccessible name, ArrReadable name, ArrSafetyPreserved name]

    havoc name arr = do
      arr' <- fresh name :: Verify (ArrBinding exp i a)
      return arr' { arr_source = arr_source arr }

    warns1 ctx name arr = arr { arr_failed = bool False }
    warns2 ctx name arr = arr {
        arr_accessible = arr_accessible arr0
      , arr_readable = arr_readable arr0
      , arr_failed = arr_failed arr0 }
      where
        arr0 :: ArrBinding exp i a
        arr0 = lookupContext name ctx

    warnLiterals name arr = [(ArrAccessible name, ok), (ArrReadable name, ok)]
      where
        ok = SMT.not (arr_failed arr)
    warnLiterals2 name _ = [ArrSafetyPreserved name]

instance (SMTEval exp a, SMTEval exp i) => IsLiteral (Literal (ArrBinding exp i a))
  where
    smtLit _   ctx (ArrAccessible name)      = arr_accessible (lookupContext name ctx :: ArrBinding exp i a)
    smtLit _   ctx (ArrReadable name)        = arr_readable (lookupContext name ctx :: ArrBinding exp i a)
    smtLit old ctx (ArrSafetyPreserved name) = case maybeLookupContext name old of
      Just (arr :: ArrBinding exp i a) ->
        arr_failed arr .||.
        SMT.not (arr_failed (lookupContext name ctx :: ArrBinding exp i a))
      Nothing -> bool False

--------------------------------------------------------------------------------

-- | A wrapper to help with fresh name generation.
newtype SMTArray exp i a = SMTArray SExpr deriving (Eq, Ord, Show, Mergeable)

instance (SMTEval exp a, SMTEval exp i) => Fresh (SMTArray exp i a)
  where
    fresh = freshSExpr

instance (SMTEval exp a, SMTEval exp i) => TypedSExpr (SMTArray exp i a)
  where
    smtType _ = tArray (smtType (undefined :: SMTExpr exp i)) (smtType (undefined :: SMTExpr exp a))
    toSMT (SMTArray arr) = arr
    fromSMT = SMTArray

arrayBindings :: Typeable (ArrBinding exp i a) => Context -> String -> [(String, ArrBinding exp i a)]
arrayBindings ctx name = filter p [ (name', y) | (Name name' _, Entry x) <- Map.toList ctx, Just y <- [cast x] ]
  where
    p (_, arr) = arr_source arr == Just name

selectArray :: (SMTEval exp a, SMTEval exp i) => SMTArray exp i a -> SMTExpr exp i -> SMTExpr exp a
selectArray arr i = fromSMT (select (toSMT arr) (toSMT i))

storeArray :: (SMTEval exp a, SMTEval exp i) => SMTExpr exp i -> SMTExpr exp a -> SMTArray exp i a -> SMTArray exp i a
storeArray i x arr = fromSMT (store (toSMT arr) (toSMT i) (toSMT x))

newArr :: forall exp i a . (Num (SMTExpr exp i), SMTOrd (SMTExpr exp i), SMTEval exp i, SMTEval exp a) => String -> SMTExpr exp i -> Verify (SMTArray exp i a)
newArr name n = do
  value <- fresh name :: Verify (SMTArray exp i a)
  let arr :: ArrBinding exp i a
      arr = ArrBinding (Just name) (bool True) (bool True) (bool False)
  poke name (ArrContents value n)
  poke name arr
  return value

peekArr :: forall exp i a . (SMTEval exp i, SMTEval exp a) => String -> Verify (Maybe (ArrBinding exp i a, String, ArrContents exp i a))
peekArr name = do
  ctx <- get
  arr <- peek name
  safe <- provable "array accessible" (arr_accessible arr)
  if safe then do
    let err = error "array accessible but has no source"
        source = fromMaybe err (arr_source arr)
    src <- peek source
    return (Just (arr, source, src))
  else do
    warn ("Unsafe use of inaccessible array " ++ name ++ " (after SwapPtr?)")
    -- Invalidate everything to help with computing the frame
    let
      refs =
        case arr_source arr of
          Nothing -> [(name, arr)]
          Just src -> arrayBindings ctx src
    forM_ refs $ \(name, arr) -> do
      arr <- havoc name arr
      poke name (arr { arr_failed = bool True } :: ArrBinding exp i a)
    return Nothing

readArr :: forall exp i a. (SMTOrd (SMTExpr exp i), Ix i, SMTEval exp i, SMTEval exp a) => String -> SMTExpr exp i -> Verify (SMTExpr exp a)
readArr name ix = do
  hintArr ix
  marr <- peekArr name
  case marr of
    Nothing -> fresh "unbound"
    Just (arr :: ArrBinding exp i a, _, src) -> do
      warning () $ do
        let
          prop = SMT.not (ix .==. skolemIndex) .||. arr_readable arr
        safe <- provable "array not modified" prop
        unless safe $ do
          warn ("Unsafe use of frozen array " ++ name)
          poke name (arr { arr_failed = bool True } :: ArrBinding exp i a)
      return (selectArray (ac_value src) ix)

updateArr :: forall exp i a.
  (Ix i, SMTEval exp i, SMTEval exp a) =>
  String ->
  (SMTArray exp i a -> SMTArray exp i a) ->
  (SMTExpr exp i -> SExpr) -> Verify ()
updateArr name update touched = do
  marr <- peekArr name
  case marr of
    Nothing -> do
      return ()
    Just (arr :: ArrBinding exp i a, source, src) -> do
      ctx <- get
      forM_ (arrayBindings ctx source \\ [(name, arr)]) $
        \(name, arr) -> do
          let readable = SMT.not (touched skolemIndex) .&&. arr_readable arr
          poke name (arr { arr_readable = readable } :: ArrBinding exp i a)
      poke name (arr { arr_readable = bool True } :: ArrBinding exp i a)
      poke source (src { ac_value = update (ac_value src) } :: ArrContents exp i a)

hintArr :: forall exp i . (SMTEval exp i, SMTOrd (SMTExpr exp i), Ix i) => SMTExpr exp i -> Verify ()
hintArr ix = do
  hint (ix .<. skolemIndex)
  hint (ix .>. skolemIndex)

--------------------------------------------------------------------------------
-- ** Predicate abstraction
--------------------------------------------------------------------------------

-- The literals used in predicate abstraction.
data SomeLiteral = forall a . IsLiteral a => SomeLiteral a

instance Eq SomeLiteral
  where
    x == y = compare x y == EQ

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
discoverInvariant :: Maybe [[SomeLiteral]] -> Verify () -> Verify (Verify (), Maybe [[SomeLiteral]], Verify ())
discoverInvariant minv body = do
  (frame, hints) <- findFrameAndHints
  (_, _, mode) <- ask
  case minv of
    Nothing | mode /= Execute -> do
      ctx <- get
      abstract ctx frame hints >>= refine frame hints
    _ -> do
      let ass = assumeLiterals frame (fromMaybe [] minv)
      ass
      return (noBreak (breaks body) >>= assume "loop terminated", minv, ass)
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
    findFrameAndHints = stack $ quietly $ noWarn $ quickly $ do
      -- Put the verifier in an arbitrary state.
      ctx <- get
      let
        op ctx (Name name _, Entry (x :: a)) = do
          val <- havoc name x
          return (insertContext name (val :: a) ctx)
      before <- foldM op Map.empty (Map.toList ctx)
      put before

      -- Run the program and see what changed.
      (_, _, hints, decls) <- fmap snd (listen body)
      after <- get

      let
        atoms (Atom x) = [x]
        atoms (List xs) = concatMap atoms xs

        hints' =
          [ Hint before hint
          | hint <- nub hints,
            null (intersect decls (atoms (hb_exp hint))) ]

      return (Map.toList (modified before after), hints')

    refine frame hints clauses = do
      ctx <- get
      clauses' <- stack $ quietly $ noWarn $ do
        assumeLiterals frame clauses
        noBreak (breaks body) >>= assume "loop not terminated" . SMT.not
        fmap (disjunction clauses) (chattily (abstract ctx frame hints))

      if clauses == clauses' then do
        printInvariant "Invariant" frame clauses
        let ass = assumeLiterals frame clauses
        ass
        return (noBreak (breaks body) >>= assume "loop terminated", Just clauses, ass)
      else refine frame hints clauses'

    assumeLiterals :: [(Name, Entry)] -> [[SomeLiteral]] -> Verify ()
    assumeLiterals frame clauses = do
      ctx <- get
      forM_ frame $ \(Name name _, Entry (_ :: a)) -> do
        val <- peek name >>= havoc name
        poke name (val :: a)
      mapM_ (\clause -> (evalClause ctx >=> assume (show clause)) clause) clauses

    abstract old frame hints = fmap (usort . map usort) $ do
      res <- quietly $ fmap concat $ mapM (Abstract.abstract (\clause -> (evalClause old >=> provable (show clause)) clause)) (lits frame)
      printInvariant "Candidate invariant" frame res
      return res
      where
        lits frame =
          partitionBy (\(SomeLiteral x) -> phase x) $
          concat [ map SomeLiteral (literals name x) | (Name name _, Entry x) <- frame ] ++
          [ SomeLiteral hint | hint <- hints, hb_type (hint_body hint) == tBool ]

    printInvariant kind frame [] =
      liftIO $
        putStrLn ("No invariant found over frame " ++ show (map fst frame))
    printInvariant kind frame clauses = liftIO $ do
      putStrLn (kind ++ " over frame " ++ show (map fst frame) ++ ":")
      sequence_ [ putStrLn ("  " ++ show clause) | clause <- clauses ]

    disjunction cs1 cs2 =
      prune (usort [ usort (c1 ++ c2) | c1 <- cs1, c2 <- cs2 ])
      where
        prune cs = [ c | c <- cs, and [ c == c' || c' \\ c /= [] | c' <- cs ] ]

    usort :: Ord a => [a] -> [a]
    usort = map head . group . sort

    partitionBy :: Ord b => (a -> b) -> [a] -> [[a]]
    partitionBy f xs = groupBy ((==) `on` f) (sortBy (comparing f) xs)

evalClause :: Context -> [SomeLiteral] -> Verify SExpr
evalClause old clause = do
  ctx <- get
  return (disj [ smtLit old ctx lit | SomeLiteral lit <- clause ])

--------------------------------------------------------------------------------
-- *** A replacement for the SMTOrd class.
--------------------------------------------------------------------------------

class SMTOrd a
  where
    (.<.)  :: a -> a -> SExpr
    (.<=.) :: a -> a -> SExpr
    (.>.)  :: a -> a -> SExpr
    (.>=.) :: a -> a -> SExpr

instance SMTEval exp a => Eq (SMTExpr exp a)
  where
    x == y = toSMT x == toSMT y

instance SMTEval exp a => Ord (SMTExpr exp a)
  where
    compare = comparing toSMT

instance SMTEval exp a => Show (SMTExpr exp a)
  where
    showsPrec n x = showsPrec n (toSMT x)

instance SMTEval exp a => Mergeable (SMTExpr exp a)
  where
    merge cond x y = fromSMT (merge cond (toSMT x) (toSMT y))

instance SMTEval exp a => ShowModel (SMTExpr exp a)
  where
    showModel x = showModel (toSMT x)

instance SMTEval exp a => Fresh (SMTExpr exp a)
  where
    fresh name = fmap fromSMT (freshVar name (smtType (undefined :: SMTExpr exp a)))

(.==.) :: TypedSExpr a => a -> a -> SExpr
x .==. y = toSMT x `eq` toSMT y

smtIte :: TypedSExpr a => SExpr -> a -> a -> a
smtIte cond x y = fromSMT (SMT.ite cond (toSMT x) (toSMT y))

--------------------------------------------------------------------------------

-- | Run a computation more chattily.
chattily :: Verify a -> Verify a
chattily = local (\(ctx, n, prove) -> (ctx, n+1, prove))

-- | Run a computation more quietly.
quietly :: Verify a -> Verify a
quietly = local (\(ctx, n, prove) -> (ctx, n-1, prove))

-- | Produce debug output.
chat :: Verify () -> Verify ()
chat mx = do
  (_, chatty, _) <- ask
  when (chatty > 0) mx

-- | Print a formula for debugging purposes.
trace :: String -> String -> SExpr -> Verify ()
trace msg kind p = chat $ do
  branch <- branch >>= mapM (lift . simplify)
  p <- lift $ simplify p
  liftIO $ do
    putStr (kind ++ " " ++ showSExpr p ++ " (" ++ msg ++ ")")
    case branch of
      []  -> putStrLn ""
      [x] -> putStrLn (" assuming " ++ showSExpr x)
      _   -> do
        putStrLn " assuming:"
        sequence_ [ putStrLn ("  " ++ showSExpr x) | x <- branch ]

-- | Print the context for debugging purposes.
printContext :: String -> Verify ()
printContext msg = do
  ctx <- get
  liftIO $ do
    putStrLn (msg ++ ":")
    forM_ (Map.toList ctx) $ \(name, val) -> putStrLn (" " ++ show name ++ " -> " ++ show val)
    putStrLn ""

--------------------------------------------------------------------------------
