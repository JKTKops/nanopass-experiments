module Passes.LispIL.LetBindThrownAtoms
  ( letBindThrownAtoms ) where

import Control.Monad.Identity

import Language.LispIL.CPS

-- | Push atoms through continuations that they are thrown to.
-- The basic idea is for (%throw <atom> (%cont (r) body)) to become
-- (%let ((r <atom>)) body). This eliminates a function from the program.
letBindThrownAtoms :: Syntax -> Syntax
letBindThrownAtoms = runIdentity . traverseCpsBU (Identity . go)

go :: Syntax -> Maybe Syntax
go (App (Cont (ContFun (Lambda x b))) a)
  | atomic a = Just $ Let (x,a) b
go _ = Nothing

atomic :: Syntax -> Bool
atomic Ref{} = True
atomic Set{} = True
atomic PtrEq{} = True
atomic Halt{} = True
atomic Delay{} = True
atomic Lambda{} = True

atomic Let{} = False
atomic Cnd{} = False
atomic App{} = False
