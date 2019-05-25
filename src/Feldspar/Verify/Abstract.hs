module Feldspar.Verify.Abstract where

import Control.Monad.Trans
import Control.Monad.Exception
import Control.Monad.Writer

import Data.List

import MiniSat hiding (withNewSolver)

--------------------------------------------------------------------------------
-- https://github.com/nick8325/imperative-edsl/blob/master/src/Language/Embedded/Verify/Abstract.hs
--------------------------------------------------------------------------------

-- Given a list of literals, and a function which checks whether a
-- disjunction of literals is provable, return the strongest provable
-- boolean formula made up from those literals (expressed as a set
-- of clauses).
abstract ::
  (Ord a, MonadIO m, MonadAsyncException m) => ([a] -> m Bool) -> [a] -> m [[a]]
abstract provable preds0 =
  fmap (filter (\ls -> length ls <= 3)) $
  execWriterT $
  withNewSolver $ \sat -> do
    let preds = nub preds0
    lits <- mapM (const (liftIO (fmap neg (newLit sat)))) preds
    let
      getClause = do
        vals <- mapM (liftIO . modelValue sat) lits
        return
          [ (pred, lit)
          | (pred, lit, val) <- zip3 preds lits vals, val /= Just False]

      predsOf clause = map fst clause
      litsOf clause  = map snd clause

      abs = do
        res <- liftIO (solve sat [])
        when res $ do
          clause <- getClause >>= maximise
          prv    <- lift (provable (predsOf clause))
          if prv then do
            shrunk <- lift (shrink (provable . predsOf) clause)
            liftIO (addClause sat (map neg (litsOf shrunk)))
            tell [predsOf shrunk]
          else do
            void (liftIO (addClause sat (lits \\ litsOf clause)))
          abs

      maximise ls = fmap (domain \\) (shrink p (domain \\ ls))
        where
          domain = zip preds lits
          p ls = liftIO (solve sat (litsOf (domain \\ ls)))

      shrink _ [] = return []
      shrink provable [l] = do
        res <- provable []
        if res then return [] else return [l]
      shrink provable ls = do
        res <- provable ls2
        if res then shrink provable ls2 else do
          ls1' <- shrink (\ls1' -> provable (ls1' ++ ls2)) ls1
          ls2' <- shrink (\ls2' -> provable (ls1' ++ ls2')) ls2
          return (ls1' ++ ls2')
        where
          (ls1, ls2) = splitAt (length ls `div` 2) ls

    abs

-- A replacement for MiniSat.withNewSolver which works in any MonadIO.
withNewSolver :: (MonadIO m, MonadAsyncException m) => (Solver -> m a) -> m a
withNewSolver h =
  do s <- liftIO newSolver
     h s `finally` liftIO (deleteSolver s)

--------------------------------------------------------------------------------
