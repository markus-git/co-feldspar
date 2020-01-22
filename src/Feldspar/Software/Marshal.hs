{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Feldspar.Software.Marshal where -- based on raw-feldspar/run/marshal

import Feldspar.Frontend (Finite(..), Indexed(..), Arrays(..), IArrays(..), value, shareM, for)
import Feldspar.Array.Vector (Manifest(..))

import Feldspar.Software (Syntax, Internal, Software, SType', SExp)
import Feldspar.Software.Primitive (SoftwarePrimType)
import Feldspar.Software.Representation (Arr, IArr)
import Feldspar.Software.Frontend (fput, fget, fprintf)

import Language.Embedded.Imperative.CMD (Formattable, Handle, stdout, stdin)

import Data.Typeable
import Data.Int
import Data.Word

import Control.Monad (ap, replicateM)

import qualified Prelude as P
import Prelude hiding (length)

--------------------------------------------------------------------------------
-- *
--------------------------------------------------------------------------------

newtype Parser a = Parser {runParser :: String -> (a,String)}

instance Functor Parser
  where
    fmap = (<$>)

instance Applicative Parser
  where
    pure  = return
    (<*>) = ap

instance Monad Parser
  where
    return a   = Parser $ \s -> (a,s)
    (>>=)  p k = Parser $ \s -> let (a,s') = runParser p s in runParser (k a) s'

readParser :: forall a . (Read a, Typeable a) => Parser a
readParser = Parser $ \s -> case reads s of
  [(a,s')] -> (a,s')
  _        -> error $ "cannot read " ++ show s

parse :: Parser a -> String -> a
parse = (fst .) . runParser

--------------------------------------------------------------------------------
-- **

class MarshalHaskell a
  where
    fromHaskell :: a -> String
    default fromHaskell :: Show a => a -> String
    fromHaskell = show

    toHaskell :: Parser a
    default toHaskell :: (Read a, Typeable a) => Parser a
    toHaskell = readParser

instance MarshalHaskell Int
instance MarshalHaskell Int8
instance MarshalHaskell Int16
instance MarshalHaskell Int32
instance MarshalHaskell Int64

instance MarshalHaskell Word
instance MarshalHaskell Word8
instance MarshalHaskell Word16
instance MarshalHaskell Word32
instance MarshalHaskell Word64

instance (MarshalHaskell a, MarshalHaskell b) => MarshalHaskell (a,b)
  where
    fromHaskell (a,b) = unwords [fromHaskell a, fromHaskell b]
    toHaskell         = (,) <$> toHaskell <*> toHaskell

instance MarshalHaskell a => MarshalHaskell [a]
  where
    fromHaskell as = unwords $ show (P.length as) : map fromHaskell as
    toHaskell      = do
        len <- toHaskell
        replicateM len toHaskell

--------------------------------------------------------------------------------
-- **

class MarshalHaskell (Haskelly a) => MarshalFeldspar a
  where
    type Haskelly a

    fwrite :: Handle -> a -> Software ()
    default fwrite :: (SType' b, Formattable b, a ~ SExp b) => Handle -> a -> Software ()
    fwrite h i = fput h "" i ""

    fread :: Handle -> Software a
    default fread :: (SType' b, Formattable b, a ~ SExp b) => Handle -> Software a
    fread = fget

writeStd :: MarshalFeldspar a => a -> Software ()
writeStd = fwrite stdout

readStd :: MarshalFeldspar a => Software a
readStd = fread stdin

instance MarshalFeldspar (SExp Int8)   where type Haskelly (SExp Int8)   = Int8
instance MarshalFeldspar (SExp Int16)  where type Haskelly (SExp Int16)  = Int16
instance MarshalFeldspar (SExp Int32)  where type Haskelly (SExp Int32)  = Int32
instance MarshalFeldspar (SExp Int64)  where type Haskelly (SExp Int64)  = Int64

instance MarshalFeldspar (SExp Word8)  where type Haskelly (SExp Word8)  = Word8
instance MarshalFeldspar (SExp Word16) where type Haskelly (SExp Word16) = Word16
instance MarshalFeldspar (SExp Word32) where type Haskelly (SExp Word32) = Word32
instance MarshalFeldspar (SExp Word64) where type Haskelly (SExp Word64) = Word64

instance (MarshalFeldspar a, MarshalFeldspar b) => MarshalFeldspar (a,b)
  where
    type Haskelly (a,b) = (Haskelly a, Haskelly b)
    fwrite h (a,b) = fwrite h a >> fprintf h " " >> fwrite h b
    fread  h       = (,) <$> fread h <*> fread h

--------------------------------------------------------------------------------
-- **

instance (MarshalHaskell (Internal a), MarshalFeldspar a, Syntax SExp a) => MarshalFeldspar (Arr a)
  where
    type Haskelly (Arr a) = [Internal a]

    fwrite h arr = do
      len :: SExp Word32 <- shareM (length arr)
      fput h "" len ""
      for 0 1 (len-1) $ \i -> do
        a <- getArr arr i
        fwrite h a
        fprintf h " "

    fread h = do
      len <- fget h
      arr <- newArr len
      for 0 1 (len-1) $ \i -> do
        a <- fread h
        setArr arr i a
      return arr

instance (MarshalHaskell (Internal a), MarshalFeldspar a, Syntax SExp a) => MarshalFeldspar (IArr a)
  where
    type Haskelly (IArr a) = [Internal a]

    fwrite h arr = do
      len :: SExp Word32 <- shareM (length arr)
      fput h "" len ""
      for 0 1 (len-1) $ \i -> do
        fwrite h ((!) arr i)
        fprintf h " "

    fread h = do
      len <- fget h
      arr <- newArr len
      for 0 1 (len-1) $ \i -> do
        a <- fread h
        setArr arr i a
      iarr <- unsafeFreezeArr arr
      return iarr

instance (MarshalHaskell (Internal a), MarshalFeldspar a, Syntax SExp a) => MarshalFeldspar (Manifest Software a)
  where
    type Haskelly (Manifest Software a) = [Internal a]

    fwrite h arr = do
      len :: SExp Word32 <- shareM (length arr)
      fput h "" len ""
      for 0 1 (len-1) $ \i -> do
        let iarr = manifest arr
        fwrite h ((!) iarr i)
        fprintf h " "

    fread h = do
      len <- fget h
      arr <- newArr len
      for 0 1 (len-1) $ \i -> do
        a <- fread h
        setArr arr i a
      iarr <- unsafeFreezeArr arr
      return (M iarr)

--------------------------------------------------------------------------------
-- **

connectStdIO :: (MarshalFeldspar a, MarshalFeldspar b) => (a -> Software b) -> Software ()
connectStdIO f = (readStd >>= f) >>= writeStd

--------------------------------------------------------------------------------
