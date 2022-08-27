{-# LANGUAGE TypeFamilies, DataKinds, EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module Language.LispIL.Syntax
  ( Syntax
  , LispILBase(Ref, Set, Cnd, Seq, App)
  ) where

import Language.LispIL

data SyntaxType
type Syntax = LispILBase SyntaxType

type instance NameIn SyntaxType = String

type instance HasVar  SyntaxType = 'False
type instance HasSExp SyntaxType = 'False

type instance HasSeq          SyntaxType = 'True
type instance HasLet          SyntaxType = 'False
type instance HasGenericPrims SyntaxType = 'True
type instance HasClosure      SyntaxType = 'False
type instance HasLambda       SyntaxType = 'False
type instance HasDelay        SyntaxType = 'False

type instance AppHead SyntaxType = Syntax

instance (ForallLispIL Show SyntaxType) => Show Syntax where
  show (Seq es)  = "(%seq " ++ unwords (map show es) ++ ")"
  show (Ref b)   = b
  show (Set b e) = "(%set! " ++ b ++ " " ++ show e ++ ")"
  show (Cnd b t f) =
    "(%cnd " ++ unwords (map show [b,t,f]) ++ ")"
  show (PtrEq x y) = "(%pointer-eq? " ++ unwords (map show [x,y]) ++ ")"
  show (Halt e) = "(%halt " ++ show e ++ ")"
  show (App hd arg) =
    "(" ++ unwords (map show [hd,arg]) ++ ")"
