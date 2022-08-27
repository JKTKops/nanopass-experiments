{-# LANGUAGE DataKinds, GADTs #-}
module Passes.LispIL.ClosureConversion (closureConversion) where

import qualified Language.LispIL         as Base
import qualified Language.LispIL.CPS     as CPS
import qualified Language.LispIL.CloConv as CC
import Language.LispIL.Binding

import Control.Monad.State.Strict
import qualified Data.IntMap as M
import qualified Data.Set as S

closureConversion :: CPS.Syntax -> Fresh CC.LiftedProgram
closureConversion = fmap ccLift . closureConvert . annotate

-------------------------------------------------------------------------------
-- Annotate the CPS tree (CC.AnnotatedSyntax is basically CPS)
-------------------------------------------------------------------------------

annotate :: CPS.Syntax -> CC.AnnotatedSyntax
annotate = snd . go where
  go :: CPS.Syntax -> (CC.FreeVars, CC.AnnotatedSyntax)
  go (CPS.Ref b@Internal{}) = (S.singleton b, CC.Ref b)
  go (CPS.Ref b)            = (S.empty, CC.Ref b)
  go (CPS.Set b e) = (S.insert b fvs, CC.Set b e')
    where (fvs, e') = go e
  go (CPS.Let (x,e) b) = (fvs, CC.Let (fvs,x,e') b')
    where (fvb, b') = go b
          (fve, e') = go e
          fvs = (fvb `S.difference` S.singleton x) <> fve
  go (CPS.Cnd b t f) = CC.Cnd <$> go b <*> go t <*> go f
  go (CPS.Halt e) = CC.Halt <$> go e
  go (CPS.PtrEq x y) = CC.PtrEq <$> go x <*> go y
  go (CPS.App hd a) = case hd of
    CPS.Force k -> 
      CC.App . CC.Force <$> go (syntaxOfCont k) <*> go a
    CPS.Term f k ->
      CC.App <$> (CC.Term <$> go f
                             <*> go (syntaxOfCont k))
             <*> go a
    CPS.Cont k ->
      CC.App . CC.Cont <$> go (syntaxOfCont k) <*> go a
  go (Base.Abs typ args body) = (fvs, Base.Abs (coerceAbsType typ) args (fvs, body'))
    where (fvs0, body') = go body
          fvs = fvs0 `S.difference` S.fromList args

syntaxOfCont :: CPS.Continuation -> CPS.Syntax
syntaxOfCont (CPS.ContVar k) = CPS.Ref k
syntaxOfCont (CPS.ContFun f) = f

coerceAbsType :: Base.HasLambda p0 ~ Base.HasLambda p1
              => Base.HasDelay p0 ~ Base.HasDelay p1
              => Base.AbsType p0 -> Base.AbsType p1
coerceAbsType Base.Lambda  = Base.Lambda
coerceAbsType Base.Promise = Base.Promise

-------------------------------------------------------------------------------
-- Perform the closure conversion (most of the work is here)
-------------------------------------------------------------------------------

closureConvert :: CC.AnnotatedSyntax -> Fresh CC.NestedSyntax
closureConvert ast
  = convert ast S.empty explode
  where explode = error "closureConvert: no top level closure"

convert :: CC.AnnotatedSyntax
        -> CC.FreeVars
        -> Binding
        -> Fresh CC.NestedSyntax
convert ast0 fvs self = cc ast0
  where
    cc :: CC.AnnotatedSyntax -> Fresh CC.NestedSyntax
    cc (CC.Ref b) = pure $ case S.lookupIndex b fvs of
      Just i  -> CC.ClosureRef (CC.Ref self) i
      Nothing -> CC.Ref b
    cc (CC.Set b e) = CC.Set b <$> cc e
    cc (CC.Let (_,x,e) b) = rebuild <$> cc e <*> cc b
      where rebuild e' b' = CC.Let (x,e') b'
    cc (CC.Cnd b t f) = CC.Cnd <$> cc b <*> cc t <*> cc f
    cc (CC.Halt e) = CC.Halt <$> cc e
    cc (CC.PtrEq x y) = CC.PtrEq <$> cc x <*> cc y
    cc (CC.App hd arg) = CC.App <$> ccAppHead hd <*> cc arg
    cc (Base.Abs typ args (newFvs,body))
      = ccAbs newFvs (coerceAbsType typ) args body

    ccAppHead :: CC.CCAppHead 'CC.Annotated -> Fresh (CC.CCAppHead 'CC.Nested)
    ccAppHead (CC.Force k) = CC.Force <$> cc k
    ccAppHead (CC.Term f k) = CC.Term <$> cc f <*> cc k
    ccAppHead (CC.Cont k)   = CC.Cont <$> cc k

    ccAbs :: CC.FreeVars
          -> Base.AbsType (CC.CloConv 'CC.Nested)
          -> [Binding]
          -> CC.AnnotatedSyntax
          -> Fresh CC.NestedSyntax
    ccAbs newFvs typ ps body = do
      newSelf <- fresh "self"
      newBody <- convert body newFvs newSelf
      cloArgs <- mapM (cc . CC.Ref) $ S.toAscList newFvs
      return $ CC.Closure (Base.Abs typ (newSelf:ps) newBody) cloArgs

-------------------------------------------------------------------------------
-- Lift closure-converted lambdas (this part is simple!)
-------------------------------------------------------------------------------

ccLift :: CC.NestedSyntax -> CC.LiftedProgram
ccLift ast = evalState liftAll $ initState ast
  where
    initState body =
      LS { nextCodePointer = 1
         , abstractionTodo = [(Base.Lambda, [], body, 0)]
         , liftedProgram   = M.empty
         }

data LS = LS { nextCodePointer :: !Int
             , abstractionTodo :: [( Base.AbsType (CC.CloConv 'CC.Nested)
                                   , [Binding], CC.NestedSyntax, CC.CodePointer)]
             , liftedProgram   :: CC.LiftedProgram
             }

type Lift = State LS
addAbstractionTodo :: Base.AbsType (CC.CloConv 'CC.Nested)
                   -> [Binding]
                   -> CC.NestedSyntax
                   -> Lift CC.CodePointer
addAbstractionTodo typ ps body = state $ \s ->
  let ptr = nextCodePointer s in
  ( ptr
  , s { nextCodePointer = ptr + 1
      , abstractionTodo = (typ,ps,body,ptr) : abstractionTodo s
      }
  )

popAbstractionTodo :: Lift (Maybe ( Base.AbsType (CC.CloConv 'CC.Nested)
                                  , [Binding]
                                  , CC.NestedSyntax
                                  , CC.CodePointer
                                  ))
popAbstractionTodo = state $ \s@LS{abstractionTodo = td} -> case td of
  []          -> (Nothing, s)
  (next:rest) -> (Just next, s {abstractionTodo = rest})

liftAll :: Lift CC.LiftedProgram
liftAll = do
  next <- popAbstractionTodo
  case next of
    Nothing -> gets liftedProgram
    Just (typ,ps,body,ptr) -> do
      lifted <- liftOne typ ps body
      modify $ \s@LS{liftedProgram=lp} ->
        s{liftedProgram = M.insert ptr lifted lp}
      liftAll

liftOne :: Base.AbsType (CC.CloConv 'CC.Nested)
        -> [Binding]
        -> CC.NestedSyntax
        -> Lift CC.LiftedSyntax
liftOne typ ps body = Base.Abs (coerceAbsType typ) ps <$> liftSyntax body

liftSyntax :: CC.NestedSyntax -> Lift CC.LiftedSyntax
liftSyntax (CC.Ref b) = pure $ CC.Ref b
liftSyntax (CC.Set b e) = CC.Set b <$> liftSyntax e
liftSyntax (CC.Let (x,e) b) = rebuild <$> liftSyntax e <*> liftSyntax b
  where rebuild e' b' = CC.Let (x,e') b'
liftSyntax (CC.Cnd b t f) = CC.Cnd <$> liftSyntax b <*> liftSyntax t <*> liftSyntax f
liftSyntax (CC.Halt e) = CC.Halt <$> liftSyntax e
liftSyntax (CC.PtrEq x y) = CC.PtrEq <$> liftSyntax x <*> liftSyntax y
liftSyntax (CC.App hd arg) = CC.App <$> liftSyntaxHd hd <*> liftSyntax arg
  where
    liftSyntaxHd (CC.Force k) = CC.Force <$> liftSyntax k
    liftSyntaxHd (CC.Term f k) = CC.Term <$> liftSyntax f <*> liftSyntax k
    liftSyntaxHd (CC.Cont k)   = CC.Cont <$> liftSyntax k
liftSyntax Base.Abs{} = error "ccLift.liftOne: Abstraction outside closure"
liftSyntax (CC.Closure (Base.Abs typ ps body) args) =
  rebuild <$> addAbstractionTodo typ ps body <*> traverse liftSyntax args
  where rebuild ptr args' = CC.Closure (coerceAbsType typ,ptr) args'
liftSyntax (CC.Closure _notAbs _) = error "ccLift.liftOne: malformed %closure"
liftSyntax (CC.ClosureRef clo ix) = CC.ClosureRef <$> liftSyntax clo <*> pure ix
