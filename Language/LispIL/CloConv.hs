{-# LANGUAGE TypeFamilies, EmptyDataDecls, DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Flat Closure-converted CPS code. Once the boilerplate generator works,
-- I want to experiment with more complicated closure layout strategies,
-- but it's too much boilerplate to do by hand right now. Sucks.
--
-- Plus I want to get onto the VM language to try the next idea.
--
-- We have three very similar sub-languages here. The first is just CPS,
-- but every abstraction is annotated with its set of free variables.
-- The second drops the annotation and makes closure construction/reference
-- explicit. The third pulls out the different lambdas into a collection
-- of top-level functions.
module Language.LispIL.CloConv
  ( module Language.LispIL.Binding
  , LispILBase(Ref,Set,Cnd,Let,PtrEq,Halt,App,Lambda,Delay
              ,AnnLambda,AnnDelay,Closure,ClosureRef)
  , CCAppHead(..)
  , CloConv, CodePointer, LiftedProgram, FreeVars
  , Stage(..), Syntax, LiftedSyntax, NestedSyntax, AnnotatedSyntax
  ) where

import qualified Data.Set as S
import qualified Data.IntMap as M

import Language.LispIL hiding (Lambda, Promise)
import qualified Language.LispIL as Base
import Language.LispIL.Binding

-- This is a convenient method for making sub-languages that are close to each
-- other if you're a human, but I don't think the generator will take this approach.
data Stage = Lifted | Nested | Annotated
data CloConv (lifting :: Stage)

type CodePointer = Int
type LiftedProgram = M.IntMap LiftedSyntax
type Syntax l     = LispILBase (CloConv l)
type LiftedSyntax = Syntax 'Lifted
type NestedSyntax = Syntax 'Nested
type AnnotatedSyntax = Syntax 'Annotated

type instance HasVar (CloConv l)          = 'False
type instance HasSExp (CloConv l)         = 'False
type instance HasSeq (CloConv l)          = 'False
type instance HasGenericPrims (CloConv l) = 'True
type instance HasLet (CloConv l)          = 'True
type instance HasLambda (CloConv l)       = 'True
type instance HasDelay (CloConv l)        = 'True
type instance HasClosure (CloConv 'Annotated) = 'False
type instance HasClosure (CloConv 'Nested) = 'True
type instance HasClosure (CloConv 'Lifted) = 'True

type instance NameIn (CloConv l) = Binding
type instance AppHead (CloConv l) = CCAppHead l

type instance LetBinding (CloConv 'Annotated)
  = (FreeVars, NameIn (CloConv 'Annotated), Syntax 'Annotated)
type instance LetBinding (CloConv 'Nested) = (Binding, NestedSyntax)
type instance LetBinding (CloConv 'Lifted) = (Binding, LiftedSyntax)

type FreeVars = S.Set Binding
type instance AbsBody (CloConv 'Annotated) = (FreeVars, Syntax 'Annotated)
type instance AbsBody (CloConv 'Nested) = Syntax 'Nested
type instance AbsBody (CloConv 'Lifted) = Syntax 'Lifted

type instance ClosureFirst (CloConv 'Nested) = NestedSyntax
type instance ClosureFirst (CloConv 'Lifted)
  = (AbsType (CloConv 'Lifted), CodePointer)
type instance ClosureKey (CloConv l) = Int

data CCAppHead l                -- (argument of the app is in brackets)
  = Force (Syntax l)            -- (%force [f] k)
  | Term  (Syntax l) (Syntax l) -- (f k [x])
  | Cont  (Syntax l)            -- (k [x])

pattern AnnLambda :: FreeVars -> Binding -> Syntax 'Annotated -> Syntax 'Annotated
pattern AnnLambda fvs x b = Abs Base.Lambda [x] (fvs, b)

pattern AnnDelay :: FreeVars -> Binding -> Syntax 'Annotated -> Syntax 'Annotated
pattern AnnDelay fvs k b = Abs Base.Promise [k] (fvs, b)
{-# COMPLETE Ref, Set, Cnd, Let, PtrEq, Halt, App, AnnLambda, AnnDelay, Closure, ClosureRef #-}

pattern Lambda :: (AbsBody (CloConv l) ~ Syntax l)
               => [Binding] -> Syntax l -> Syntax l
pattern Lambda args b = Abs Base.Lambda args b

pattern Delay :: (AbsBody (CloConv l) ~ Syntax l)
              => [Binding] -> Syntax l -> Syntax l
pattern Delay args b = Abs Base.Promise args b
{-# COMPLETE Ref, Set, Cnd, Let, PtrEq, Halt, App, Lambda, Delay, Closure, ClosureRef #-}

instance (ForallLispIL Show (CloConv 'Lifted)) => Show LiftedSyntax where
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
  show (Delay args body)
    = "(%delay (" ++ unwords (map show args) ++ ") " ++ show body ++ ")"
  show (Lambda args body)
    = "(%lambda (" ++ unwords (map show args) ++ ") " ++ show body ++ ")"
  show (Closure (typ,ptr) args)
    = prefix ++ unwords (show ptr : map show args) ++ ")"
    where prefix = case typ of
            Base.Lambda  -> "(%closure "
            Base.Promise -> "(%promise "
  show (ClosureRef clos key)
    = "(%closure-ref " ++ unwords [show clos, show key] ++ ")"

instance Show (AbsType (CloConv 'Lifted)) where
  show _ = error "Show@(AbsType (CloConv 'Lifted)): no."

instance Show (CCAppHead 'Lifted) where
  show _ = error "Show@CC.CCAppHead: no."
