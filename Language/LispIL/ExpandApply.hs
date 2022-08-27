{-# LANGUAGE TypeFamilies, DataKinds, EmptyDataDecls, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.LispIL.ExpandApply
  ( Syntax
  , LispILBase( Ref, Set, Cnd, Seq, App, Let
              , Language.LispIL.ExpandApply.Abs, PtrEq)
  , AppOf(..)

  , module Language.LispIL.Binding
  ) where

import Language.LispIL hiding (Abs)
import qualified Language.LispIL as Base
import Language.LispIL.Binding

data ExpandApply
type Syntax = LispILBase ExpandApply

type instance NameIn ExpandApply = Binding

type instance HasVar ExpandApply = 'False
type instance HasSExp ExpandApply = 'False
type instance HasSeq ExpandApply = 'True
type instance HasLet ExpandApply = 'True
type instance HasGenericPrims ExpandApply = 'True
type instance HasClosure ExpandApply = 'False
type instance HasLambda ExpandApply = 'False
type instance HasDelay ExpandApply = 'True

type instance LetBinding ExpandApply = [(NameIn ExpandApply, Syntax)]
type instance AppHead ExpandApply = AppOf
type instance AbsBody ExpandApply = Syntax

data AppOf = Force | Term Syntax

pattern Abs :: Syntax -> Syntax
pattern Abs es = Base.Abs Promise [] es
{-# COMPLETE Ref, Set, Cnd, PtrEq, Seq, App, Let, Abs #-}

instance (ForallLispIL Show ExpandApply) => Show Syntax where
  show (Seq es) = "(%seq " ++ unwords (map show es) ++ ")"
  show (Let bs body) = "(%let (" ++ unwords (map showBinding bs) ++ ") " ++ show body ++ ")"
  show (Ref b)  = show b
  show (Set b e) = "(%set! " ++ show b ++ " " ++ show e ++ ")"
  show (Cnd b t f) =
    "(%cnd " ++ unwords (map show [b,t,f]) ++ ")"
  show (PtrEq x y) = "(%pointer-eq? " ++ unwords (map show [x,y]) ++ ")"
  show (Halt e) = "(%halt " ++ show e ++ ")"
  show (App hd x) = "(" ++ show hd ++ " " ++ show x ++ ")"
  show (Abs body) = "(%delay " ++ show body ++ ")"

instance Show (AbsType ExpandApply) where
  show Promise = "%delay"
  -- show Lambda = GHC knows this can't happen!

instance Show AppOf where
  show Force = "%force"
  show (Term t) = show t

showBinding :: (NameIn ExpandApply, Syntax) -> String
showBinding (b,e) = "(" ++ show b ++ " " ++ show e ++ ")"
