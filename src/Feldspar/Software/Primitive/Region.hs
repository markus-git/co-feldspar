{-# language GADTs                 #-}
{-# language StandaloneDeriving    #-}
{-# language TypeOperators         #-}
{-# language FlexibleInstances     #-}
{-# language FlexibleContexts      #-}
{-# language UndecidableInstances  #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies          #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Feldspar.Software.Primitive.Region where

import Data.Maybe (mapMaybe)

import Control.Monad.State
import Control.Monad.Reader

-- syntactic.
import Language.Syntactic
import Language.Syntactic.Functional
--import Language.Syntactic.Functional.Tuple
import qualified Language.Syntactic as Syn

--------------------------------------------------------------------------------

type Var = String

type Type = ()

data Region a
  where
    ERgn :: Maybe Var -> [Var] -> Region a

data Prim sig
  where
    FreeVar :: Var -> Prim (Full a)
    Lit :: (Show a, Eq a) => a -> Prim (Full a)
    Add :: Num a => Prim (a :-> a :-> Full a)

    Cond :: Prim (Bool :-> a :-> a :-> Full a)

    Pair :: Prim (a :-> b :-> Full (a, b))
    Fst  :: Prim ((a, b) :-> Full a)
    Snd  :: Prim ((a, b) :-> Full b)

type Exp = Prim :&: Region

--------------------------------------------------------------------------------

type Env    = [(Var, Scheme)]
type Scheme = ([Var], [Qual], Type)
data Qual   = Put Type

type Context = [(Var, Qual)]
type TSubst  = [(Var, Type)]

type M = ReaderT Env (State Int)

runM :: M a -> a
runM = flip evalState 0 . flip runReaderT []

--------------------------------------------------------------------------------

class Infer sym
  where
    inferSym ::
      sym sig ->
      Args (AST sym) sig ->
      M (ASTF (sym :&: Region) (DenResult sig))
    
inferASTM :: Infer sym => ASTF sym sig -> M (ASTF (sym :&: Region) sig)
inferASTM = simpleMatch inferSym

inferAST :: Infer sym => ASTF sym sig -> ASTF (sym :&: Region) sig
inferAST = runM . inferASTM

--------------------------------------------------------------------------------

instance Infer Prim
  where
    inferSym a@(FreeVar v) (Nil) = do
      env <- ask
      case lookup v env of
        Nothing         -> error "!"
        Just (vs, _, _) -> return $ Sym (a :&: ERgn Nothing vs)
    inferSym l@(Lit v) (Nil) =
      return $ Sym (l :&: ERgn Nothing [])
    inferSym (Add) (a :* b :* Nil) = do
      am <- inferASTM a
      bm <- inferASTM b
      return $ Sym (Add :&: ERgn Nothing (getRgn am ++ getRgn bm)) :$ am :$ bm
    inferSym (Cond) (c :* t :* f :* Nil) = do
      cm <- inferASTM c
      tm <- inferASTM t
      fm <- inferASTM f
      let sub :: Var -> Var -> Var -> Maybe Var
          sub x y z = if y == z then Just x else Nothing
      case (getScalar tm, getScalar fm) of
        (Just a,  Just b)  -> do
          return $ Sym (Cond :&: ERgn (Just a) [])
            :$ cm :$ tm :$ substitute (sub a b) fm
        (Nothing, Nothing) -> do
          return $ Sym (Cond :&: ERgn Nothing [])
            :$ cm :$ tm :$ fm
        (_, _) -> error "!!"
    inferSym (Pair) (a :* b :* Nil) = undefined
    inferSym (Fst) (pair :* Nil) = do
      pairm <- inferASTM pair
      return $ Sym (Fst :&: ERgn Nothing (getRgn pairm)) :$ pairm
    inferSym (Snd) (pair :* Nil) = undefined

--------------------------------------------------------------------------------

substitute ::
  (Var -> Maybe Var) ->
  AST (sym :&: Region) sig ->
  AST (sym :&: Region) sig
substitute sub (Sym (s :&: ERgn m vs)) = Sym (s :&: ERgn m' vs')
  where
    m'   = maybe m sub m
    vs'  = mapMaybe sub vs
      -- map (\v -> case sub v of Just v -> v | Nothing -> v) vs
substitute sub (f :$ a) = substitute sub f :$ substitute sub a

getRgn :: AST (sym :&: Region) sig -> [Var]
getRgn (Sym f)  = unRgn $ decorInfo f
getRgn (f :$ _) = getRgn f

unRgn :: Region a -> [Var]
unRgn (ERgn _ vs) = vs

getScalar :: AST (sym :&: Region) sig -> Maybe Var
getScalar (Sym f)  = unScalar $ decorInfo f
getScalar (f :$ _) = getScalar f

unScalar :: Region a -> Maybe Var
unScalar (ERgn v _) = v

--------------------------------------------------------------------------------
