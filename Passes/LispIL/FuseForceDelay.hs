module Passes.LispIL.FuseForceDelay (fuseForceDelay) where

import Data.Functor.Identity
import Language.LispIL.CPS

-- This pass fuses "apparent promises" which are immediately forced.
-- Roughly; FFD[[(%send (%force (%delay (dk) b_dk)) k)]]
--          = (%let (dk k) b_dk)
fuseForceDelay :: Syntax -> Syntax
fuseForceDelay = runIdentity . traverseCpsTD (Identity . go)

go :: Syntax -> Maybe Syntax
go (App (Force k) (Delay dk b)) = Just $ Let (dk,syntaxK) b
  where syntaxK = case k of
          ContVar kv -> Ref kv
          ContFun f  -> f
go _ = Nothing
