{-# LANGUAGE TupleSections, RecordPuns #-}
module TH.QuoteLanguage where

import TH.LinguistRegistry
import TH.LanguageFamilyRepr

import Control.Monad (replicateM)
import Language.Haskell.TH.Syntax
import Data.Foldable (fold)
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

quoteLanguage :: Quotable a => Name -> Q a -> Q a
quoteLanguage langName thing = do
  mLangRepr <- lookupLanguage langName
  case mLangRepr of
    Nothing -> fail $ "Can't quote `" ++ show langName ++ "' without a representation."
    Just langRepr -> thing >>= quote langRepr

langConstrs :: Fin Language -> H.HashMap Name (Fin LangConstr)
langConstrs lang = fold $ nonterminalConstrs <$> langNonterminals lang

ntType :: LanguageTag -> Name -> Type
ntType tag ntName = AppT (ConT ntName) (ConT tag)

resultTyOfConstr :: Fin Language -> Name -> Type
resultTyOfConstr repr constrName =
  let LangConstr{constrSrcNt} = langConstrs repr H.! constrName
  in ntType (langName repr) constrSrcNt

class Quotable a where
  quote :: Fin Language -> a -> Q a

instance Quotable Pat where
  quote repr = go where
    go (LitP l) = pure (LitP l)
    go (VarP n) = pure (VarP n)
    go (TupP ps) = TupP <$> traverse go ps
    go (UnboxedTupP ps) = UnboxedTupP <$> traverse go ps
    go (UnboxedSumP p alt arity) = (\p' -> UnboxedSumP p' alt arity) <$> go p
    go (ConP conName pats)
      | conName `S.member` constrs = 
        -- TH just does the right thing^tm if there's only one thing in the list
        (\ps' -> SigP (ConP conName [TupP ps']) (resultTyOfConstr repr conName))
        <$> traverse go pats
      | otherwise = ConP conName <$> traverse go pats
    go (InfixP p1 n p2) = InfixP <$> go p1 <*> pure n <*> go p2
    go (UInfixP p1 n p2) = UInfixP <$> go p1 <*> pure n <*> go p2
    go (ParensP p) = ParensP <$> go p
    go (TildeP p) = TildeP <$> go p
    go (BangP p) = BangP <$> go p
    go (AsP n p) = AsP n <$> go p
    go WildP = pure WildP
    go (RecP n fps) = RecP n <$> traverse goFieldPat fps
    go (ListP ps) = ListP <$> traverse go ps
    go (SigP p ty) = SigP <$> go p <*> quote repr ty
    go (ViewP e p) = ViewP <$> quote repr e <*> go p

    goFieldPat (n,p) = (n,) <$> go p

    constrs = H.keysSet $ langConstrs repr

instance Quotable Type where
  quote repr = go where
    go (ForallT tvars cxt ty) = ForallT tvars <$> traverse go cxt <*> go ty
    go (AppT ty1 ty2) = AppT <$> go ty1 <*> go ty2
    go (SigT ty k) = SigT <$> go ty <*> go k
    go (VarT n) = pure (VarT n)
    go (ConT tyConName)
      | tyConName `S.member` nts
      = pure $ AppT (ConT tyConName) (ConT (langName repr))
      | otherwise = pure $ ConT tyConName
    go (PromotedT n)         = pure $ PromotedT n
    go (InfixT ty1 n ty2)    = InfixT <$> go ty1 <*> pure n <*> go ty2
    go (UInfixT ty1 n ty2)   = UInfixT <$> go ty1 <*> pure n <*> go ty2
    go (ParensT ty)          = ParensT <$> go ty
    go (TupleT size)         = pure $ TupleT size
    go (UnboxedTupleT size)  = pure $ UnboxedTupleT size
    go (UnboxedSumT arity)   = pure $ UnboxedSumT arity
    go ArrowT                = pure ArrowT
    go EqualityT             = pure EqualityT
    go ListT                 = pure ListT
    go (PromotedTupleT size) = pure $ PromotedTupleT size
    go PromotedNilT          = pure PromotedNilT
    go PromotedConsT         = pure PromotedConsT
    go StarT                 = pure StarT
    go ConstraintT           = pure ConstraintT
    go (LitT tylit)          = pure $ LitT tylit
    go WildCardT             = pure WildCardT
    
    nts = H.keysSet $ langNonterminals repr

instance Quotable Exp where
  quote repr = go where
    go (VarE n) = pure $ VarE n
    go (ConE dataConName)
      -- TODO: One way to make this significantly nicer would be to also
      -- create pattern synonyms (with mkName) for every constr (at each language)
      -- and store their names in the repr (ouch!). This is also made less
      -- awful when we stop tupling constructors that don't need to be tupled.
      -- Then here we just replace the data con name with the pattern synonym!
      | dataConName `H.member` constrs
      = do let arity = length $ constrContents $ constrs H.! dataConName
           pats <- replicateM arity $ newName "x"
           return $ LamE (map VarP pats) 
                    $ SigE (AppE (ConE dataConName) $ TupE (map VarE pats))
                           (resultTyOfConstr repr dataConName)
      | otherwise = pure $ ConE dataConName
    go (LitE lit)         = pure $ LitE lit
    go (AppE hd end)      = AppE <$> go hd <*> go end
    go (AppTypeE e t)     = AppTypeE <$> go e <*> quote repr t
    go (InfixE me1 e2 me3)
      = InfixE <$> traverse go me1 <*> go e2 <*> traverse go me3
    go (UInfixE e1 e2 e3) = UInfixE <$> go e1 <*> go e2 <*> go e3
    go (ParensE e)        = ParensE <$> go e
    go (LamE pats b)      = LamE <$> traverse (quote repr) pats <*> go b
    go (LamCaseE matches) = LamCaseE <$> traverse (quote repr) matches
    go (TupE es)          = TupE <$> traverse go es
    go (UnboxedTupE es)   = UnboxedTupE <$> traverse go es
    go (UnboxedSumE e alt arity)
      = (\e' -> UnboxedSumE e' alt arity) <$> go e
    go (CondE e1 e2 e3)   = CondE <$> go e1 <*> go e2 <*> go e3
    go (MultiIfE gsAndEs) = MultiIfE <$> traverse goGAndE gsAndEs
    go (LetE decs b)      = LetE <$> traverse (quote repr) decs <*> go b
    go (CaseE e ms)       = CaseE <$> go e <*> traverse (quote repr) ms
    go (DoE stmts)        = DoE <$> traverse (quote repr) stmts
    go (CompE stmts)      = CompE <$> traverse (quote repr) stmts
    go (ArithSeqE range)  = ArithSeqE <$> quote repr range
    go (ListE es)         = ListE <$> traverse go es
    go (SigE e t)         = SigE <$> go e <*> quote repr t
    go (RecConE n fes)    = RecConE n <$> traverse goFE fes
    go (RecUpdE e fes)    = RecUpdE <$> go e <*> traverse goFE fes
    go (StaticE e)        = StaticE <$> go e
    go (UnboundVarE n)    = pure $ UnboundVarE n
    go (LabelE str)       = pure $ LabelE str

    goGAndE (guard,e) = (,) <$> quote repr guard <*> go e
    goFE (n,e) = (n,) <$> go e
    constrs = langConstrs repr

instance Quotable Match where
  quote repr (Match p b ds)
    = Match <$> quote repr p
            <*> quote repr b
            <*> traverse (quote repr) ds

instance Quotable Dec where
  quote repr = go where
    go (FunD n cs) = FunD n <$> traverse (quote repr) cs
    go (ValD p b ds)
      = ValD <$> quote repr p
             <*> quote repr b
             <*> traverse go ds
    go (DataD cxt n bndrs mk cons derivs)
      = (\cxt' cons' derivs' -> DataD cxt' n bndrs mk cons' derivs')
        <$> traverse (quote repr) cxt
        <*> traverse (quote repr) cons
        <*> traverse (quote repr) derivs
    go (NewtypeD cxt n bndrs mk con derivs)
      = (\cxt' con' derivs' -> NewtypeD cxt' n bndrs mk con' derivs')
        <$> traverse (quote repr) cxt
        <*> quote repr con
        <*> traverse (quote repr) derivs
    go (TySynD n bndrs ty) = TySynD n bndrs <$> quote repr ty
    go (ClassD cxt n bndrs fundeps ds)
      = (\cxt' ds' -> ClassD cxt' n bndrs fundeps ds')
        <$> traverse (quote repr) cxt
        <*> traverse go ds
    go (InstanceD mo cxt ty ds)
      = InstanceD mo <$> traverse (quote repr) cxt
                     <*> quote repr ty
                     <*> traverse go ds
    go (SigD n ty) = SigD n <$> quote repr ty
    go (ForeignD f) = ForeignD <$> quote repr f
    go (InfixD fixity n) = pure $ InfixD fixity n
    go (PragmaD prag) = PragmaD <$> quote repr prag
    go (DataFamilyD n bndrs mk) = pure $ DataFamilyD n bndrs mk
    go (DataInstD cxt n tys mk cons derivs)
      = (\cxt' tys' cons' derivs' -> DataInstD cxt' n tys' mk cons' derivs')
        <$> traverse (quote repr) cxt
        <*> traverse (quote repr) tys
        <*> traverse (quote repr) cons
        <*> traverse (quote repr) derivs
    go (NewtypeInstD cxt n tys mk con derivs)
      = (\cxt' tys' con' derivs' -> NewtypeInstD cxt' n tys' mk con' derivs')
        <$> traverse (quote repr) cxt
        <*> traverse (quote repr) tys
        <*> quote repr con
        <*> traverse (quote repr) derivs
    go (TySynInstD n eqn) = TySynInstD n <$> quote repr eqn
    go (OpenTypeFamilyD tfh) = pure $ OpenTypeFamilyD tfh
    go (ClosedTypeFamilyD tfh eqns)
      = ClosedTypeFamilyD tfh <$> traverse (quote repr) eqns
    go (RoleAnnotD n rs) = pure $ RoleAnnotD n rs
    go (StandaloneDerivD mstrat cxt ty)
      = StandaloneDerivD <$> traverse (quote repr) mstrat
                         <*> traverse (quote repr) cxt
                         <*> quote repr ty
    go (DefaultSigD n ty) = DefaultSigD n <$> quote repr ty
    go (PatSynD n args dir pat)
      = PatSynD n args <$> quote repr dir
                       <*> quote repr pat
    go (PatSynSigD n pst) = PatSynSigD n <$> quote repr pst

instance Quotable Stmt where
  quote repr = go where
    go (BindS pat exp) = BindS <$> quote repr pat <*> quote repr exp
    go (LetS ds) = LetS <$> traverse (quote repr) ds
    go (NoBindS exp) = NoBindS <$> quote repr exp
    go (ParS stmtss) = ParS <$> traverse (traverse go) stmtss

instance Quotable Range where
  quote repr = go where
    goE :: Exp -> Q Exp
    goE = quote repr

    go (FromR e)              = FromR <$> goE e
    go (FromThenR e1 e2)      = FromThenR <$> goE e1 <*> goE e2
    go (FromToR e1 e2)        = FromToR <$> goE e1 <*> goE e2
    go (FromThenToR e1 e2 e3) = FromThenToR <$> goE e1 <*> goE e2 <*> goE e3

instance Quotable Guard where
  quote repr (NormalG e) = NormalG <$> quote repr e
  quote repr (PatG ss) = PatG <$> traverse (quote repr) ss

instance Quotable Body where
  quote repr (GuardedB gs) = GuardedB <$> traverse (quote repr) gs
  quote repr (NormalB e)   = NormalB <$> quote repr e

instance Quotable Clause where
  quote repr (Clause pats b ds)
    = Clause <$> traverse (quote repr) pats
             <*> quote repr b
             <*> traverse (quote repr) ds

instance Quotable Con where
  quote repr (NormalC n bts) = NormalC n <$> traverse (quote repr) bts
  quote repr (RecC n vbts) = RecC n <$> traverse (quote repr) vbts
  quote repr (InfixC bt1 n bt2)
    = InfixC <$> quote repr bt1
             <*> pure n
             <*> quote repr bt2
  quote repr (ForallC bndrs cxt con)
    = ForallC bndrs <$> traverse (quote repr) cxt
                    <*> quote repr con
  quote repr (GadtC ns bts ty)
    = GadtC ns <$> traverse (quote repr) bts
               <*> quote repr ty
  quote repr (RecGadtC ns vbts ty)
    = RecGadtC ns <$> traverse (quote repr) vbts
                  <*> quote repr ty

instance Quotable DerivClause where
  quote repr (DerivClause mstrat cxt)
    = DerivClause <$> traverse (quote repr) mstrat
                  <*> traverse (quote repr) cxt

instance Quotable Foreign where
  quote repr (ImportF cc saf f n ty) = ImportF cc saf f n <$> quote repr ty
  quote repr (ExportF cc f n ty) = ExportF cc f n <$> quote repr ty

instance Quotable Pragma where
  quote repr = go where
    go p@InlineP{} = pure p
    go (SpecialiseP n ty mi ps)
      = (\ty' -> SpecialiseP n ty' mi ps) <$> quote repr ty
    go (SpecialiseInstP ty) = SpecialiseInstP <$> quote repr ty
    go (RuleP n rbs e1 e2 ps)
      = RuleP n <$> traverse (quote repr) rbs
                <*> quote repr e1
                <*> quote repr e2
                <*> pure ps
    go (AnnP target e) = AnnP target <$> quote repr e
    go p@LineP{} = pure p
    go p@CompleteP{} = pure p

instance Quotable TySynEqn where
  quote repr (TySynEqn as rhs)
    = let goT = quote repr :: Type -> Q Type
      in TySynEqn <$> traverse goT as <*> goT rhs

instance Quotable DerivStrategy where
  quote repr (ViaStrategy ty) = ViaStrategy <$> quote repr ty
  quote _repr strat = pure strat

instance Quotable PatSynDir where
  quote repr (ExplBidir cs) = ExplBidir <$> traverse (quote repr) cs
  quote _repr dir = pure dir

instance (Quotable a, Quotable b) => Quotable (a,b) where
  quote repr (a,b) = (,) <$> quote repr a <*> quote repr b

instance (Quotable a, Quotable b, Quotable c) => Quotable (a,b,c) where
  quote repr (a,b,c) = (,,) <$> quote repr a <*> quote repr b <*> quote repr c

instance Quotable Bang where
  quote _repr bang = pure bang

instance Quotable Name where
  quote _repr name = pure name

instance Quotable RuleBndr where
  quote repr (TypedRuleVar n ty) = TypedRuleVar n <$> quote repr ty
  quote _repr bndr = pure bndr

instance Quotable a => Quotable [a] where
  quote repr = traverse (quote repr)
