module Passes.LispIL.AtomPropagation (atomPropagation) where

import Control.Monad.State.Strict
import Data.Functor (($>))
import qualified Data.IntMap.Strict as M
import Data.Maybe (fromMaybe)

import Language.LispIL.CPS

type VarMap = M.IntMap
insert :: Binding -> v -> VarMap v -> VarMap v
insert External{} _ m = m
insert (Internal _n i) v m = M.insert i v m

insertWith :: (v -> v -> v) -> Binding -> v -> VarMap v -> VarMap v
insertWith _f External{} _ = id
insertWith f (Internal _n i) v = M.insertWith f i v

(!?) :: VarMap v -> Binding -> Maybe v
_m !? External{} = Nothing
m  !? Internal _n i = m M.!? i

type Propagate = State (VarMap Syntax)
-- This pass wants to propagate all bindings of suitably "small"
-- simple terms to their use sites.
-- If the binding variable is only used once, _any_ atom will be
-- propagated, including abstractions.
-- There is a technical reason that this is undesirable. Pushing an abstraction
-- down the tree ("lambda dropping") can increase the number of free variables
-- of intervening abstractions, increasing their closure size. This comes with
-- a runtime cost, either at the point of building the closure (flat conversion)
-- or the point of access (linked conversion). For this experiment compiler, we
-- don't really care about that, and propagating abstractions tends to lead to
-- some very impactful further optimization.
-- 
-- If the binding variable is used more than once, only Refs are propagated.
--
-- Notice that counting variable references
-- is influenced by running the CopyCoalesce pass! Currently we run CopyCoalesce
-- before Atom Propagation 1 and that seems to do the trick, but it's probably
-- desirable to schedule it after passes that might introduce nonhomogenous
-- use-def chains.

atomPropagation :: Syntax -> Syntax
atomPropagation tree = evalState (traverseCpsTD go tree) M.empty
  where
    counts = countAllUses tree

    go :: Syntax -> Propagate (Maybe Syntax)
    go (Ref b)       = gets (!? b)
    go (Let (x,e) b)
      | atomic e = case fromMaybe 0 $ counts !? x of
          0 -> -- evaluation of x is atomic and unused, so toss it.
               -- I guess this should technically go under DCE? Hm.
               pure $ Just b
          1 -> -- atomic and used once, propagate and delete binding.
               modify (insert x e) $> Just b
          _n -> -- used many times, only propagate if ref.
                case e of
                  Ref{} -> modify (insert x e) $> Just b
                  _ -> pure Nothing
    go _ = pure Nothing

-- | Establish a mapping from bindings to how frequently they are used.
-- Conveniently, this type of analysis pass can be expressed as a traversal.
countAllUses :: Syntax -> VarMap Int
countAllUses = flip execState M.empty . traverseCpsTD go
  where go :: Syntax -> State (VarMap Int) (Maybe Syntax)
        go (Ref b) = modify (insertWith (+) b 1) $> Nothing
        go _       = pure Nothing


-- | Determine if an expression is atomic.
-- Atomic expressions are side-effect free.
atomic :: Syntax -> Bool
atomic Ref{} = True
atomic Set{} = False
atomic (Cnd b t f) = atomic b && atomic t && atomic f
atomic (PtrEq x y) = atomic x && atomic y
atomic Halt{}      = False
atomic App{}       = False
-- A let expression technically could be atomic, but we don't
-- want to propagate them anyways so we just say they aren't.
atomic (Let (_x,e) b) = atomic e && atomic b
atomic Lambda{}    = True
atomic Delay{}     = True
