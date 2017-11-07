{-# language GADTs               #-}
{-# language TypeOperators       #-}
{-# language PatternSynonyms     #-}
{-# language ViewPatterns        #-}
{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}

module Feldspar.Software.Optimize where

import Feldspar.Representation
import Feldspar.Software.Primitive
import Feldspar.Software.Expression

import Data.Struct
import Data.Selection

import Control.Monad.Writer hiding (Any (..))
import Data.Maybe
import Data.Constraint (Dict (..))
import Data.Set (Set)
import qualified Data.Monoid as Monoid
import qualified Data.Set as Set

-- syntactic.
import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Tuple
import Language.Syntactic.Functional.Sharing

-- debug.
import Debug.Trace

--------------------------------------------------------------------------------
-- * Optimize software expressions.
--------------------------------------------------------------------------------

viewLit :: ASTF SoftwareDomain a -> Maybe a
viewLit lit | Just (Lit a) <- prj lit = Just a
viewLit _ = Nothing

witInteger :: ASTF SoftwareDomain a -> Maybe (Dict (Integral a, Ord a))
witInteger a = case getDecor a of
  ValT (Node Int8ST)   -> Just Dict
  ValT (Node Int16ST)  -> Just Dict
  ValT (Node Int32ST)  -> Just Dict
  ValT (Node Int64ST)  -> Just Dict
  ValT (Node Word8ST)  -> Just Dict
  ValT (Node Word16ST) -> Just Dict
  ValT (Node Word32ST) -> Just Dict
  ValT (Node Word64ST) -> Just Dict
  _ -> Nothing

isExact :: ASTF SoftwareDomain a -> Bool
isExact = isJust . witInteger

-- | projection with a stronger constraint to allow using it in
--   bidirectional patterns.
prjBi :: (sub :<: sup) => sup sig -> Maybe (sub sig)
prjBi = prj


--------------------------------------------------------------------------------

pattern SymP t s <- Sym ((prjBi -> Just s) :&: ValT t)
  where
    SymP t s = Sym ((inj s) :&: ValT t)

pattern VarP t v <- Sym ((prjBi -> Just (VarT v)) :&: t)
  where
    VarP t v = Sym (inj (VarT v) :&: t)

pattern LamP t v body <- Sym ((prjBi -> Just (LamT v)) :&: t) :$ body
  where
    LamP t v body = Sym (inj (LamT v) :&: t) :$ body


--------------------------------------------------------------------------------

pattern LitP :: () => (Eq a, Show a)
  => STypeRep a -> a -> ASTF SoftwareDomain a
  
pattern AddP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern SubP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern MulP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern NegP :: () => (Num a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a

pattern DivP :: () => (Integral a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

pattern ModP :: () => (Integral a, SoftwarePrimType a)
  => STypeRep a -> ASTF SoftwareDomain a -> ASTF SoftwareDomain a
  -> ASTF SoftwareDomain a

--------------------------------------------------------------------------------

pattern NonLitP <- (viewLit -> Nothing)

pattern LitP t a <- Sym ((prj -> Just (Lit a)) :&: ValT t)
  where
    LitP t a = Sym (inj (Lit a) :&: ValT t)

pattern AddP t a b <- SymP t Add :$ a :$ b
  where
    AddP t a b = simplifyUp $ SymP t Add :$ a :$ b
  
pattern SubP t a b <- SymP t Sub :$ a :$ b
  where
    SubP t a b = simplifyUp $ SymP t Sub :$ a :$ b

pattern MulP t a b <- SymP t Mul :$ a :$ b
  where
    MulP t a b = simplifyUp $ SymP t Mul :$ a :$ b

pattern NegP t a <- SymP t Neg :$ a
  where
    NegP t a = simplifyUp $ SymP t Neg :$ a

pattern DivP t a b <- SymP t Div :$ a :$ b
  where
    DivP t a b = simplifyUp $ SymP t Div :$ a :$ b

pattern ModP t a b <- SymP t Mod :$ a :$ b
  where
    ModP t a b = simplifyUp $ SymP t Mod :$ a :$ b

--------------------------------------------------------------------------------

simplifyUp :: ASTF SoftwareDomain a -> ASTF SoftwareDomain a
-- Addition with zero.
simplifyUp (AddP t (LitP _ 0) b) | isExact b = b
simplifyUp (AddP t a (LitP _ 0)) | isExact a = a
-- Simplify additions with literals.
simplifyUp (AddP t (AddP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (b+c))
simplifyUp (AddP t (SubP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (c-b))
simplifyUp (AddP t a (LitP _ b)) | Just Dict <- witInteger a, b < 0
  = SubP t a (LitP t (negate b))
-- Subtraction with zero.
simplifyUp (SubP t (LitP _ 0) b) | isExact b = NegP t b
simplifyUp (SubP t a (LitP _ 0)) | isExact a = a
-- Simplify subtractions with literals.
simplifyUp (SubP t (AddP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = AddP t a (LitP t (b-c))
simplifyUp (SubP t (SubP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = SubP t a (LitP t (b+c))
simplifyUp (SubP t a (LitP _ b)) | Just Dict <- witInteger a, b < 0
  = AddP t a (LitP t (negate b))
-- Multiplication with zero.
simplifyUp (MulP t (LitP _ 0) b) | isExact b = LitP t 0
simplifyUp (MulP t a (LitP _ 0)) | isExact a = LitP t 0
-- Multiplication with one.
simplifyUp (MulP t (LitP _ 1) b) | isExact b = b
simplifyUp (MulP t a (LitP _ 1)) | isExact a = a
-- Simplify multiplications with literals.
simplifyUp (MulP t (MulP _ a (LitP _ b)) (LitP _ c)) | isExact a
  = MulP t a (LitP t (b*c))
-- Simplify negations.
simplifyUp (NegP t (NegP _ a))   | isExact a = a
simplifyUp (NegP t (AddP _ a b)) | isExact a = SubP t (NegP t a) b
simplifyUp (NegP t (SubP _ a b)) | isExact a = SubP t b a
simplifyUp (NegP t (MulP _ a b)) | isExact a = MulP t a (NegP t b)
-- Move literals to the right.
simplifyUp (AddP t a@(LitP _ _) b@NonLitP) | isExact a = AddP t b a
simplifyUp (SubP t a@(LitP _ _) b@NonLitP) | isExact a = AddP t (NegP t b) a
simplifyUp (MulP t a@(LitP _ _) b@NonLitP) | isExact a = MulP t b a
-- Simplify not-expressions.
-- Not sure (yet) why I can't write `simplifyUp (NotP _ (NotP _ a)) = a`
simplifyUp (SymP _ Not :$ (SymP _ Not :$ a)) = a
simplifyUp (SymP t Not :$ (SymP _ Lt :$ a :$ b))
  = simplifyUp $ SymP t Gte :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Gt :$ a :$ b))
  = simplifyUp $ SymP t Lte :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Lte :$ a :$ b))
  = simplifyUp $ SymP t Gt :$ a :$ b
simplifyUp (SymP t Not :$ (SymP _ Gte :$ a :$ b))
  = simplifyUp $ SymP t Lt :$ a :$ b
-- Simplify and-expressions.
simplifyUp (SymP _ And :$ LitP t False :$ _) = LitP t False
simplifyUp (SymP _ And :$ _ :$ LitP t False) = LitP t False
simplifyUp (SymP _ And :$ LitP t True :$ b)  = b
simplifyUp (SymP _ And :$ a :$ LitP t True)  = a
-- Simplify or-expressions.
simplifyUp (SymP _ Or :$ LitP t False :$ b) = b
simplifyUp (SymP _ Or :$ a :$ LitP t False) = a
simplifyUp (SymP _ Or :$ LitP t True :$ _)  = LitP t True
simplifyUp (SymP _ Or :$ _ :$ LitP t True)  = LitP t True
-- Simplify conditional expressions.
simplifyUp (SymP _ Cond :$ LitP _ True  :$ t :$ _)  = t
simplifyUp (SymP _ Cond :$ LitP _ False :$ _ :$ f)  = f
simplifyUp (SymP _ Cond :$ c :$ t :$ f) | equal t f = t
-- Simplify pairs.
simplifyUp (SymP t Pair :$ (SymP _ Fst :$ a) :$ (SymP _ Snd :$ b))
    | alphaEq a b
    , ValT t' <- getDecor a
    , Just Dict <- softwareTypeEq t t' = a
simplifyUp (SymP t Fst :$ (SymP _ Pair :$ a :$ _)) = a
simplifyUp (SymP t Snd :$ (SymP _ Pair :$ _ :$ a)) = a
-- 
simplifyUp a | bug ("fold: " ++ show a) = constFold a
  -- `constFold` here ensures that `simplifyUp` does not produce any expressions
  -- that can be statically constant folded. This property is needed, e.g. to
  -- fully simplify the expression `negate (2*x)`. The simplification should go
  -- as follows:
  --
  --     negate (2*x)  ->  negate (x*2)  ->  x * negate 2  ->  x*(-2)
  --
  -- There is no explicit rule for the last step; it is done by `constFold`.
  -- Furthermore, this constant folding would not be performed by `simplifyM`
  -- since it never sees the sub-expression `negate 2`. (Note that the constant
  -- folding in `simplifyM` is still needed, because constructs such as
  -- `ForLoop` cannot be folded by simple literal propagation.)
  --
  -- In order to see that `simplifyUp` doesn't produce any "junk"
  -- (sub-expressions that can be folded by `constFold`), we reason as follows:
  --
  --   * Assume that the arguments of the top-level node are junk-free
  --   * `simplifyUp` will either apply an explicit rewrite or apply `constFold`
  --   * In the latter case, the result will be junk-free
  --   * In case of an explicit rewrite, the resulting expression is constructed
  --     by applying `simplifyUp` to each newly introduced node; thus the
  --     resulting expression must be junk-free


--------------------------------------------------------------------------------

-- | Reduce an expression to a literal if the following conditions are met:
--
-- * The top-most symbol can be evaluated statically (i.g. not a variable or a
--   lifted side-effecting program)
-- * All immediate sub-terms are literals
-- * The type of the expression is an allowed type for literals (e.g. not a
--   function)
--
-- Note that this function only folds the top-level node of an expressions (if
-- possible). It does not reduce an expression like @1+(2+3)@ where the
-- sub-expression @2+3@ is not a literal.
constFold :: ASTF SoftwareDomain a -> ASTF SoftwareDomain a
constFold e
    | constArgs e, canFold e, ValT t@(Node _) <- getDecor e
    = LitP t (evalClosed e)
  where
    canFold :: ASTF SoftwareDomain a -> Bool
    canFold = simpleMatch (\(s :&: ValT _) _ -> go s)
      where
        go :: SoftwareConstructs sig
           -> Bool
        go var | Just (FreeVar _)         <- prj var = False
        go ix  | Just (ArrIx _)           <- prj ix  = False
        go bid | Just (_ :: BindingT sig) <- prj bid = False
        go _   = True
constFold e = e

-- | Check whether all arguments of a symbol are literals
constArgs :: AST SoftwareDomain sig -> Bool
constArgs (Sym _)         = True
constArgs (s :$ LitP _ _) = constArgs s
constArgs _               = False


--------------------------------------------------------------------------------

type Opt = Writer (Set Name, Monoid.Any)

freeVar :: Name -> Opt ()
freeVar v = tell (Set.singleton v, mempty)

bindVar :: Name -> Opt a -> Opt a
bindVar v = censor (\(vars, unsafe) -> (Set.delete v vars, unsafe))

tellUnsafe :: Opt ()
tellUnsafe = tell (mempty, Monoid.Any True)

simplifyM :: ASTF SoftwareDomain a -> Opt (ASTF SoftwareDomain a)
simplifyM exp = case exp of
    (VarP _ v)      -> freeVar v >> return exp
    (LamP t v body) -> bindVar v $ fmap (LamP t v) $ simplifyM body
    _               -> simpleMatch (\s@(v :&: t) args ->
      do (exp', (vars, Monoid.Any unsafe)) <- listen
           (simplifyUp . appArgs (Sym s) <$> mapArgsM simplifyM args)
         case () of
           _ | Just (FreeVar _) <- prj v -> tellUnsafe >> return exp'
           _ | Just (ArrIx _)   <- prj v -> tellUnsafe >> return exp'
           _ | null vars && not unsafe, ValT t'@(Node _) <- t
             -> return $ LitP t' $ evalClosed exp'
           _ -> return exp'
      )
      exp
  -- Array indexing is actually not unsafe. It's more like
  -- an expression with a free variable. But setting the
  -- unsafe flag does the trick.
  -- Constant fold if expression is closed and does not
  -- contain unsafe operations.

bug :: String -> Bool
bug = flip trace True

--------------------------------------------------------------------------------

optimize :: ASTF SoftwareDomain a -> ASTF SoftwareDomain a
optimize = fst . runWriter . simplifyM


--------------------------------------------------------------------------------
