{-# LANGUAGE TypeFamilies, DataKinds, ConstraintKinds, UndecidableInstances #-}
{-# LANGUAGE GADTs, ScopedTypeVariables #-}
module Language.LispIL where

import Data.Kind (Constraint)

data LispILBase pass where
  -- Source constructors
  Var  :: (HasVar  pass ~ 'True) => NameIn pass -> LispILBase pass
  SExp :: (HasSExp pass ~ 'True) => [LispILBase pass] -> LispILBase pass

  -- Some independent built-ins
  Seq :: (HasSeq pass ~ 'True) => [LispILBase pass] -> LispILBase pass
  Let :: (HasLet pass ~ 'True)
    => LetBinding pass -> LispILBase pass
    -> LispILBase pass

  -- Generic built-ins
  Ref :: (HasGenericPrims pass ~ 'True) => NameIn pass -> LispILBase pass
  Set :: (HasGenericPrims pass ~ 'True) => NameIn pass -> LispILBase pass -> LispILBase pass
  Cnd :: (HasGenericPrims pass ~ 'True) 
    => LispILBase pass -> LispILBase pass -> LispILBase pass
    -> LispILBase pass
  Halt :: (HasGenericPrims pass ~ 'True) => LispILBase pass -> LispILBase pass
  PtrEq :: (HasGenericPrims pass ~ 'True)
    => LispILBase pass -> LispILBase pass
    -> LispILBase pass
  App :: (HasGenericPrims pass ~ 'True)
    -- we're only supporting one-argument applications for now
    -- further experimentation will be easier if the templating stuff
    -- actually works.
    => AppHead pass -> LispILBase pass
    -> LispILBase pass
  
  -- Abstraction
  -- Note sure if the HasAbs class is actually necessary.
  --   GHC might be smart enough to go "well if HasLambda pass and
  --   HasDelay pass are both 'False, there are no patterns to match"
  --   but I doubt it because AbsType is still inhabited by bottom.
  Abs :: (HasAbs pass ~ 'True)
    => AbsType pass
    -> [NameIn pass] -> AbsBody pass
    -> LispILBase pass
  
  -- Closure stuff
  Closure :: (HasClosure pass ~ 'True)
    => ClosureFirst pass -> [LispILBase pass]
    -> LispILBase pass
  ClosureRef :: (HasClosure pass ~ 'True)
    => LispILBase pass -- some expression which should evaluate to a closure;
                   -- I don't think this can be statically guaranteed :(
    -> ClosureKey pass -- covers both %closure-ref and %closure-link
                       -- as well as maybe an earlier phase where they are
                       -- still names!
    -> LispILBase pass

type family NameIn pass :: *

type family HasVar pass :: Bool
type family HasSExp pass :: Bool
type family HasSeq pass :: Bool
type family HasLet pass :: Bool
type family HasGenericPrims pass :: Bool
type family HasClosure pass :: Bool

type family LetBinding pass :: *

type family AppHead pass :: *

data AbsType pass where
  Lambda  :: (HasLambda pass ~ 'True) => AbsType pass
  Promise :: (HasDelay  pass ~ 'True) => AbsType pass

type family HasLambda pass :: Bool
type family HasDelay pass  :: Bool

type family HasAbs pass :: Bool where
  HasAbs pass = Or (HasLambda pass) (HasDelay pass)

type family Or (x :: Bool) (y :: Bool) :: Bool where
  Or 'True _ = 'True
  Or _ 'True = 'True
  Or _ _     = 'False

type family AbsBody pass :: *

type family ClosureFirst pass :: *
type family ClosureKey pass :: *

type family OnlyIf (b :: Bool) (c :: Constraint) where
  OnlyIf 'True c = c
  OnlyIf 'False c = ()

type ForallLispIL c p =
  ( c (LispILBase p), c (NameIn p)
  , OnlyIf (HasLet p) (c (LetBinding p))
  , OnlyIf (HasGenericPrims p) (c (AppHead p))
  , OnlyIf (HasAbs p) (c (AbsType p), c (AbsBody p))
  , OnlyIf (HasClosure p) (c (ClosureFirst p), c (ClosureKey p)))

-- We want functions to perform a top-down traversal of a LispIL tree.
-- The structure as written for this experiment can't handle
-- bottom-up traversals. I'd have to be able to say "transform all of the
-- children to LispILBase out, then I'll rebuild this node as a LispILBase out
-- and ask you to transform it." But that doesn't work, because the transformer
-- has to start at LispILBase in.
--
-- The solution is to index the base types with _two_ passes, a pass for
-- this node and a pass for its children. The structure can be such that they
-- can only disagree at the root of the tree (during the traversal, the root
-- will eventually be everywhere!)
-- 
-- Then the transformer looks like either (top-down)
--   LispILBase in in -> Maybe (LispILBase out in)
-- or (bottom-up)
--   LispILBase in out -> Maybe (LispILBase out out)
-- and of course all of that should be monadic.
--
-- The auto-boilerplate system probably wants some way to know how to
-- (or be given) default transformations between the child types that can
-- change. Alternatively, since good nanopass design wouldn't need strange
-- defaults, we can can require SomeChild in ~ SomeChild out.
--
-- Actually, that's not good enough, because the child types might contain
-- more LispILBases that need to be recursed through. I suspect that the
-- eventual code generator will end up just emitting all the code for each
-- traversal separately. Maybe it could try and identify ones that can share
-- a body to keep code size down.
