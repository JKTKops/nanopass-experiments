{-# LANGUAGE TypeFamilies, DataKinds, EmptyDataDecls, UndecidableInstances #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.LispIL.CPS
  ( Syntax, CPS
  , LispILBase( Ref, Set, Cnd, PtrEq, Halt
              , App, Let, Lambda, Delay)
  , AppOf(..), Continuation(..)
  , traverseCpsBU, traverseCpsTD

  , module Language.LispIL.Binding
  )
  where

import Control.Monad ((>=>), (<=<))

import Language.LispIL hiding (Lambda)
import qualified Language.LispIL as Base
import Language.LispIL.Binding

data CPS
type Syntax = LispILBase CPS

type instance NameIn CPS = Binding

type instance HasVar CPS = 'False
type instance HasSExp CPS = 'False
type instance HasSeq CPS = 'False
type instance HasLet CPS = 'True
type instance HasGenericPrims CPS = 'True
type instance HasClosure CPS = 'False
type instance HasLambda CPS = 'True
type instance HasDelay CPS = 'True

-- note the dropping of []
type instance LetBinding CPS = (NameIn CPS, Syntax)
type instance AppHead CPS = AppOf
type instance AbsBody CPS = Syntax

-- These lambdas are always continuations (this implementation of LispIL
-- straight-up does not support external lambdas, the builtins need to be
-- defined in the runtime) so the Binding is always the single continuation
-- argument.
pattern Lambda :: NameIn CPS -> Syntax -> Syntax
pattern Lambda n e = Abs Base.Lambda [n] e

-- In contrast, promises have no real arguments, but they do take a continuation
-- in CPS, so this one argument is the ContVar.
--
-- I'm definitely curious how the boilerplate generator will want to work
-- in this kind of situation; we end up with definitions that look like
--   (abs lambda (x) e)
--   (abs promise (k) e)
-- where abs,lambda,promise are literals (=> patterns?) and x,k are
-- var and contvar respectively and e is syntax.
-- So it's more than just the pass that determines what can go in the body
-- of the abs. It's the whole constructor itself. In a simple case like this,
-- it's actually kinda good enough to do something like
-- data Lambda; data Promise
-- type family Abs1 cas :: *; type instance Abs1 Lambda = LambdaKeyword
-- type family Abs2 cas :: *; type instance Abs2 Lambda = NameIn pass
--                            type instance Abs2 Promise = ContVar
-- This probably isn't the best way to represent LispIL anyway, but there
-- are languages cases where it is. How powerful to make the metalanguage?
-- unclear.
pattern Delay :: NameIn CPS -> Syntax -> Syntax
pattern Delay k e = Abs Promise [k] e
{-# COMPLETE Ref, Set, Cnd, PtrEq, App, Let, Lambda, Delay #-}

data AppOf
  = Force Continuation        -- (%force f k)
  | Term  Syntax Continuation -- (f k x)
  | Cont  Continuation

-- In a system with both in and out indices, we could pretty easily incorporate
-- a different index K here. Continuation would be LispILBase K CPS!
-- Auto-generated traversals wouldn't dive into these, because they can't.
-- They don't know how. But... it might actually be possible, with sufficient
-- restrictions stating that LispILBase K is a strict subset of LispILBase CPS.
data Continuation
  = ContVar (NameIn CPS) -- k
  | ContFun Syntax       -- probably always a Lambda, idk

instance (ForallLispIL Show CPS) => Show Syntax where
  show (Ref n) = show n
  show (Set n e) = "(%set! " ++ show n ++ " " ++ show e ++ ")"
  show (Let (x,e) b) = "(%let (" ++ show x ++ " " ++ show e ++ ") " ++ show b ++ ")"
  show (Cnd b t f) = "(%cnd " ++ unwords (map show [b,t,f]) ++ ")"
  show (PtrEq x y) = "(%pointer-eq? " ++ unwords (map show [x,y]) ++ ")"
  show (Halt e) = "(%halt " ++ show e ++ ")"
  show (App hd x) = case hd of
    Force k  -> "(%send (%force " ++ show x ++ ") " ++ show k ++ ")"
    Term f k -> "(%send (" ++ unwords [show f, show x] ++ ") " ++ show k ++ ")"
    Cont k   -> "(%throw " ++ unwords [show x, show k] ++ ")"
  show (Delay k body) = "(%delay (" ++ show k ++ ") " ++ show body ++ ")"
  show (Lambda x body) = "(%lambda (" ++ show x ++ ") " ++ show body ++ ")"

instance Show Continuation where
  show (ContVar b) = show (Ref b :: Syntax)
  show (ContFun s) = show s

instance Show (AbsType CPS) where
  show _ = error "Show@(AbsType CPS): no."

instance Show AppOf where
  show _ = error "Show@CPS.AppOf: no."

-- | Traverse a CPS Syntax structure in a bottom-up fashion.
-- The transformer should return 'Nothing' to indicate that it doesn't
-- wish to modify a node, and should return 'Just newNode' to modify it.
-- It may assume that all children of the presented node are already transformed,
-- and that the ancestors are not.
traverseCpsBU :: Monad m => (Syntax -> m (Maybe Syntax)) -> Syntax -> m Syntax
traverseCpsBU = traverseCPSGeneric (>=>)

-- | Traverse a CPS Syntax structure in a top-down fashion.
-- The transformer should return 'Nothing' to indicate that it doesn't
-- wish to modify a node, and should return 'Just newNode' to modify it.
--
-- The transformer is iterated on each node until it returns Nothing. This
-- ensures that it is safe to delete a node, replacing it with one of its children,
-- and trust that the replacement will still be inspected by the pass.
--
-- It may assume that all ancestors of the passed node (and siblings to the left)
-- have already been transformed, and that the children have not.
traverseCpsTD :: Monad m => (Syntax -> m (Maybe Syntax)) -> Syntax -> m Syntax
traverseCpsTD = traverseCPSGeneric (<=<)

traverseCPSGeneric :: forall m. Monad m 
                   => (forall a. (a -> m a) -> (a -> m a) -> (a -> m a))
                   -> (Syntax -> m (Maybe Syntax)) -> Syntax -> m Syntax
traverseCPSGeneric order = trav where
  trav transform = syntax where
    fNode node = do
      mnode' <- transform node
      case mnode' of
        Nothing    -> return node
        -- iterate until Nothing.
        Just node' -> fNode node'

    syntax :: Syntax -> m Syntax
    syntax = traverseSyntax `order` fNode
    
    traverseSyntax :: Syntax -> m Syntax
    traverseSyntax (Ref b) = pure $ Ref b
    traverseSyntax (Set b e) = Set b <$> syntax e
    traverseSyntax (Cnd b t f) = Cnd <$> syntax b <*> syntax t <*> syntax f
    traverseSyntax (Let (x,e) b) = rebuild <$> syntax e <*> syntax b
      where rebuild e' b' = Let (x,e') b'
    traverseSyntax (PtrEq x y) = PtrEq <$> syntax x <*> syntax y
    traverseSyntax (Halt e) = Halt <$> syntax e
    traverseSyntax (Abs typ k body) = Abs typ k <$> syntax body
    traverseSyntax (App hd arg) = App <$> appOf hd <*> syntax arg

    appOf (Force k) = Force <$> continuation k
    appOf (Term f k) = Term <$> syntax f <*> continuation k
    appOf (Cont k) = Cont <$> continuation k

    continuation (ContVar k) = do s <- syntax $ Ref k
                                  case s of
                                    Ref k' -> pure $ ContVar k'
                                    other  -> pure $ ContFun other
    continuation (ContFun f) = ContFun <$> syntax f
