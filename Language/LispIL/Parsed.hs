{-# LANGUAGE TypeFamilies, EmptyDataDecls, DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.LispIL.Parsed
  ( LispIL
  , LispILBase(Var, SExp)
  ) where

import Language.LispIL

data Parsed

type LispIL = LispILBase Parsed

type instance NameIn Parsed = String

type instance HasVar  Parsed = 'True
type instance HasSExp Parsed = 'True

type instance HasSeq Parsed = 'False
type instance HasLet Parsed = 'False
type instance HasGenericPrims Parsed = 'False
type instance HasLambda Parsed = 'False
type instance HasDelay  Parsed = 'False
type instance HasClosure Parsed = 'False

instance (ForallLispIL Show Parsed) => Show LispIL where
  show (Var v) = v
  show (SExp ts) = "(" ++ unwords (map show ts) ++ ")"
