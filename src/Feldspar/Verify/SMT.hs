module Feldspar.Verify.SMT
  ( module Feldspar.Verify.SMT
  , module SimpleSMT
  )
  where

import Data.List

import Control.Monad.State.Strict
import Control.Applicative

import SimpleSMT(
    SExpr(..), Result(..), Value(..)
  , bool, int, real, fun, fam, ite
  , tBool, tInt, tReal, tArray, tBits
  , select, store, concat, extract
  , bvULt, bvULeq, bvSLt, bvSLeq, bvNeg, bvAdd, bvSub, bvMul, bvUDiv
  , bvURem, bvSDiv, bvSRem, bvAnd, bvOr, bvNot, bvXOr, bvShl, bvAShr, bvLShr
  , signExtend, zeroExtend, realDiv
  , add, sub, mul, neg, abs, lt, leq, gt, geq, implies)
--  , newLogger)
import qualified SimpleSMT as SMT

--------------------------------------------------------------------------------
-- * Simple SMT front-end.
--------------------------------------------------------------------------------

type SMT = StateT SMTState IO

data SMTState = SMTState {
    st_solver :: SMT.Solver
  , st_next   :: Integer }

runZ3 :: [String] -> SMT a -> IO a
runZ3 args m = do
  -- logger <- fmap Just (newLogger 0)
  let logger = Nothing
  solver <- SMT.newSolver "z3" (["-smt2", "-in"] ++ args) logger
  evalStateT m (SMTState solver 0)

freshNum :: SMT Integer
freshNum = do
  st <- get
  put st { st_next = st_next st + 1 }
  return (st_next st)

withSolver :: (SMT.Solver -> SMT a) -> SMT a
withSolver k = do
  st <- get
  k (st_solver st)

stack :: SMT a -> SMT a
stack m = withSolver $ \solver ->
  lift (SMT.push solver) *> m <* lift (SMT.pop solver)

not :: SExpr -> SExpr
not p
  | p == bool True  = bool False
  | p == bool False = bool True
  | otherwise = SMT.not p

conj :: [SExpr] -> SExpr
conj xs | bool False `elem` xs = bool False
conj [] = bool True
conj [x] = x
conj xs = fun "and" xs

disj :: [SExpr] -> SExpr
disj xs | bool True `elem` xs = bool True
disj [] = bool False
disj [x] = x
disj xs = fun "or" xs

(.||.), (.&&.) :: SExpr -> SExpr -> SExpr
x .||. y = disj [x, y]
x .&&. y = conj [x, y]

eq :: SExpr -> SExpr -> SExpr
eq x y
  | x == y = bool True
  | otherwise = SMT.eq x y

setOption :: String -> String -> SMT ()
setOption opt val = withSolver $ \solver -> lift (SMT.setOption solver opt val)

getExpr :: SExpr -> SMT Value
getExpr exp = withSolver $ \solver -> lift (SMT.getExpr solver exp)

assert :: SExpr -> SMT ()
assert expr = withSolver $ \solver -> lift (SMT.assert solver expr)

simplify :: SExpr -> SMT SExpr
simplify expr = withSolver $ \solver -> lift (SMT.command solver (fun "simplify" [expr]))

assertSimp :: SExpr -> SMT ()
assertSimp expr = simplify expr >>= assert

check :: SMT Result
check = withSolver $ \solver -> lift (SMT.check solver)

declare :: String -> SExpr -> SMT SExpr
declare name ty = withSolver $ \solver -> lift (SMT.declare solver name ty)

declareFun :: String -> [SExpr] -> SExpr -> SMT SExpr
declareFun name args res = withSolver $ \solver -> lift (SMT.declareFun solver name args res)

declareSort :: String -> SMT ()
declareSort name = withSolver $ \solver -> lift (SMT.simpleCommand solver ["declare-sort", name])

--------------------------------------------------------------------------------
-- ** Show SMT expressions.
--------------------------------------------------------------------------------

showSExpr :: SExpr -> String
showSExpr exp = SMT.showsSExpr exp ""

showValue :: Value -> String
showValue (Bool x)   = show x
showValue (Int x)    = show x
showValue (Real x)   = show x
showValue (Bits _ x) = show x
showValue (Other x)  = showSExpr x

showArray :: Value -> SExpr -> SMT String
showArray n arr = do
    vals <- sequence [ getExpr (select arr i) | i <- take cutoff (indexes n) ]
    if length (take (cutoff+1) (indexes n)) <= cutoff
    then
      return ("{" ++ intercalate ", " (map showValue vals) ++ "}")
    else
      return ("{" ++ intercalate ", " (map showValue vals) ++ ", ...}")
  where
    cutoff :: Int
    cutoff = 20

    indexes :: Value -> [SExpr]
    indexes (Int n)    = map int [0..n-1]
    indexes (Bits w n) = map (bits w) [0..n-1]

bits :: Int -> Integer -> SExpr
bits w n = List [Atom "_", Atom ("bv" ++ show m), int (fromIntegral w)]
  where
    m = n `mod` (2^w)

--------------------------------------------------------------------------------
