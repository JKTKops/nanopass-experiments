{-|
Simple Dead Code Elimination for LispIL. Code is considered dead if
  it is the unused branch of a (%cnd (%pointer-eq x y)) form where
  the test is statically true or false.
-}
module Passes.LispIL.DCE
  ( dce ) where

import Data.Functor.Identity

import Language.LispIL.CPS

dce :: Syntax -> Syntax
dce = runIdentity . traverseCpsTD (Identity . go)

go :: Syntax -> Maybe Syntax
go (Cnd (PtrEq (Ref a) (Ref b)) t f) = case ptreq a b of
  Yes   -> Just t
  No    -> Just f
  Maybe -> Nothing
go _ = Nothing

data PointerEquality = Yes | No | Maybe

ptreq :: Binding -> Binding -> PointerEquality
ptreq (External a) (External b)
  | a == b    = Yes
  | otherwise = No
ptreq (Internal _n i) (Internal _m j)
  | i == j    = Yes
ptreq _ _     = Maybe
