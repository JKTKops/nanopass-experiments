module Passes.LispIL.CPST
  ( cpsTransform ) where

import Language.LispIL.ExpandApply hiding (Syntax)
import Language.LispIL.CPS hiding (Syntax)
import qualified Language.LispIL.ExpandApply as In
import qualified Language.LispIL.CPS         as Out

cpsTransform :: In.Syntax -> Fresh Out.Syntax
cpsTransform ast = do
  r <- fresh "_"
  let cont = ContFun $ Lambda r $ Halt (Ref r)
  cps ast cont

cps :: In.Syntax -> Continuation -> Fresh Out.Syntax
cps (Ref n) k = pure $ App (Cont k) (Ref n)
cps (Set n e) k = cpsOne e $ \r -> pure $ App (Cont k) (Set n r)
cps (Cnd b t f) k = do
  cndk <- fresh "cnd-k"
  let k' = ContVar cndk
  cpsOne b $ \bk ->
    Let (cndk, continuation2syntax k) <$>
      (Cnd bk <$> cps t k' <*> cps f k')
-- Once again, true nanopass would've had a separate pass pull apart flat
-- let bindings into nested bindings, but that's too much boilerplate.
-- Surprisingly, the part that _really_ gets me isn't the type family
-- boilerplate. It's writing the Show instances. We'll definitely want the
-- metaprograms to include at least functional Dump instances, if not full
-- Pretty instances (for the lisp-like structure they are defined with, anyway).
cps (Let [] body) k = cps body k
cps (Let ((x,e):bs) body) k = do
  cpsOne e $ \cpsE ->
    Let (x,cpsE) <$> cps (Let bs body) k
cps (Seq es) k = cpsList es $ \cpsEs -> pure $ App (Cont k) (last cpsEs)
cps (PtrEq x y) k = do
  cpsList [x,y] $ \es -> case es of
    [cpsX, cpsY] -> pure $ App (Cont k) (PtrEq cpsX cpsY)
    _ -> error "impossible result from cpsList"
-- This case discards k; it ends the program!
cps (Halt e) _k = cpsOne e $ \cpsE -> pure $ Halt cpsE
cps (Abs body) k = do
  dk <- fresh "dk"
  cpsBody <- cps body (ContVar dk)
  return $ App (Cont k) (Delay dk cpsBody)
cps (App In.Force p) k = cpsOne p $ pure . App (Out.Force k)
cps (App (In.Term f) x) k =
  cpsOne f $ \cpsF ->
    cpsOne x $ \cpsX ->
      pure $ App (Out.Term cpsF k) cpsX

cpsList :: [In.Syntax] -> ([Out.Syntax] -> Fresh Out.Syntax) -> Fresh Out.Syntax
cpsList [] consume = consume []
cpsList (ast:asts) consume = cpsOne ast $ \astr ->
  cpsList asts $ \astsr -> consume (astr:astsr)

cpsOne :: In.Syntax -> (Out.Syntax -> Fresh Out.Syntax) -> Fresh Out.Syntax
cpsOne ast consume = do
  r <- fresh "r"
  contBody <- consume (Ref r)
  cps ast $ ContFun $ Lambda r contBody

continuation2syntax :: Continuation -> Out.Syntax
continuation2syntax (ContVar b) = (Ref b)
continuation2syntax (ContFun k) = k
