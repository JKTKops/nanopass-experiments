{-# LANGUAGE GADTs, ConstraintKinds, KindSignatures, FlexibleInstances #-}
module Passes.LispIL
  ( parser, buildAST, insertApply, expandApply
  , cpsTransform, letBindThrownAtoms, copyCoalesce
  , atomPropagation, dce, fuseForceDelay

  , runFresh
  , PipelineC(..), Pipeline, executeOn, debugOn, pipeline
  ) where

import System.Console.ANSI
import Data.Kind (Constraint)

import Language.LispIL.Binding hiding (fresh)
import qualified Language.LispIL.Parsed as Parsed
import qualified Language.LispIL.CloConv as CC

import Passes.LispIL.Parse
import Passes.LispIL.BuildAST
import Passes.LispIL.InsertApply
import Passes.LispIL.ExpandApply
import Passes.LispIL.CPST
import Passes.LispIL.LetBindThrownAtoms
import Passes.LispIL.CopyCoalesce
import Passes.LispIL.AtomPropagation
import Passes.LispIL.DCE
import Passes.LispIL.FuseForceDelay
import Passes.LispIL.ClosureConversion

data PipelineC (c :: * -> Constraint) now eventually where
  Stop :: PipelineC c now now
  Then :: (c now, c next)
       => (String, now -> next) -- ^ name and impl of phase
       -> PipelineC c next eventual -- ^ Rest of the schedule
       -> PipelineC c now eventual

infixr 9 `Then`

class NoConstraint a
instance NoConstraint a

type Pipeline = PipelineC NoConstraint

executeOn :: PipelineC c now eventually -> now -> eventually
executeOn Stop now = now
executeOn (Then (_,f) sched) now = executeOn sched (f now)

debugOn :: PipelineC Show now eventually -> now -> IO eventually
debugOn Stop now = do
  setSGR [SetColor Foreground Vivid Green]
  putStrLn "Pipeline complete!"
  setSGR [Reset]
  return now
debugOn ((name,f) `Then` rest) now = do
  let next = f now
  setSGR [SetColor Foreground Vivid Cyan]
  putStrLn $ "Phase: " ++ name
  setSGR [Reset]
  print next
  debugOn rest next

-- I don't want to deal with natural-transformative monadic scheduling so
-- we have to finagle the types for the Fresh transformations a bit.

parseOrFail :: String -> Parsed.LispIL
parseOrFail inp = case parser inp of
  Left e  -> error $ show e
  Right v -> v

newtype FreshIntermediate a = FI { getFI :: (a,Int) }
instance Show a => Show (FreshIntermediate a) where
  showsPrec n m = showsPrec n (fst (getFI m))

initFresh :: (a -> Fresh b) -> (a -> FreshIntermediate b)
initFresh f a = FI $ runFreshFrom 0 (f a)

fresh :: (a -> Fresh b) -> (FreshIntermediate a -> FreshIntermediate b)
fresh f (FI (a,c)) = FI $ runFreshFrom c (f a)

preserve :: (a -> b) -> (FreshIntermediate a -> FreshIntermediate b)
preserve f (FI (a,c)) = FI (f a,c)

expire :: (a -> Fresh b) -> (FreshIntermediate a -> b)
expire f (FI (a,c)) = fst $ runFreshFrom c (f a)

pipeline :: PipelineC Show String CC.LiftedProgram
pipeline = ("Parse", parseOrFail)
    `Then` ("Build AST", buildAST)
    `Then` ("Insert Apply", insertApply)
    `Then` ("Expand Apply", initFresh expandApply)
    `Then` ("Continuation Passing Style Transform", fresh cpsTransform)
    `Then` ("Fuse Throw", preserve letBindThrownAtoms)
    `Then` ("Copy Coalesce", preserve copyCoalesce)
    `Then` ("Atom Propagation 1", preserve atomPropagation)
    `Then` ("Dead Code Elimination", preserve dce)
    `Then` ("Atom Propagation 2", preserve atomPropagation)
    `Then` ("Fuse Force-Delay", preserve fuseForceDelay)
    `Then` ("Atom Propagation 3", preserve atomPropagation)
    `Then` ("Fuse Throw", preserve letBindThrownAtoms)
    `Then` ("Atom Propagation 4", preserve atomPropagation)
    `Then` ("Closure Conversion", expire closureConversion)
    `Then` Stop
