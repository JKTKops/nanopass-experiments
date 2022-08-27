module Passes.LispIL.BuildAST
  ( buildAST ) where

import Language.LispIL.Parsed hiding (LispIL)
import Language.LispIL.Syntax
import qualified Language.LispIL.Parsed as Parsed

buildAST :: Parsed.LispIL -> Syntax
buildAST (Var n) = Ref n
buildAST (SExp [a@SExp{}, e]) =
  App (buildAST a) (buildAST e)
buildAST (SExp (Var hd : es)) = case hd of
  "begin" -> Seq es'
  "set!"  -> case es of
    [Var toSet, e] -> Set toSet (buildAST e)
    _ -> error "Passes.LispIL.BuildAST: malformed set! form"
  "if"    -> case es of
    [b,t,f] -> Cnd (buildAST b) (buildAST t) (buildAST f)
    _ -> error "Passes.LispIL.BuildAST: malformed if form"
  _ -> case es of
    [e] -> App (Ref hd) (buildAST e)
    _ -> error "Passes.LispIL.BuildAST: malformed application (not exactly 1 arg)"
  where es' = map buildAST es
buildAST (SExp _) = error "Passes.LispIL.BuildAST: malformed application (not exactly 1 arg)"
