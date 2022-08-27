{-# LANGUAGE PatternSynonyms, ViewPatterns, NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TupleSections #-}
module TH.DefinePass where

import Control.Monad ((>=>))
import qualified Control.Monad.Writer as W
import qualified Data.DList as DL

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Ppr (split)

import Data.List (groupBy, sortOn, partition)

import TH.QuoteLanguage (quote)
import TH.LinguistRegistry (lookupLanguage, LanguageRep)
import Data.Maybe (mapMaybe)

{-
The difficulty here is picking how to abuse existing Haskell syntax to define passes.

  -- EDIT: It turns out that this is trickier than I thought.. Template Haskell quote forces
  -- the renaming pass, which we don't really care about. It raises an error on type sigs
  -- without accompanying bindings.
  --
  -- For the pass def itself, we can write twoArmIf (R ir) = ir and set that up to work
  -- correctly. For a named (but otherwise auto-generated) pass, you'd have to either write
  -- one case or we'd have to support an explicit syntax for that (name = auto, for example).

One method that I'm particularly partial to at the moment is to not use local
definition syntax for our own purposes. All of the definitions in a pass can be
translated into a local structure. For example:

definePass [d|
  twoArmIf :: Simple -> TwoArmIf

  exp :: Transform' Exp Exp
  exp (If (R b) (R t) (Just (R f))) = If b t f
  exp (If (R b) (R t) Nothing) = If b t (Exp 0)

  {- Alternative definition of exp:
  exp :: Transform' Exp Exp
  exp (If (R b) (R t) (R f)) = If b t (fromMaybe 0 f)

  The catamorpher knows the type of f is Maybe (Exp lang) and uses
  'fmap exp' to catamorph it instead of plain exp.
  Monadic and applicative versions TBD.
  -}

  -- Actually, the above definition might be _required_. It's not clear in
  -- Just (R f) how we can identify the type of f. If this were allowed,
  -- it would probably have to be with an explicit type annotation, like
  -- (R f :: Exp) or (R (f :: Exp)) (probably either would be acceptable).
 |]

this can be translated into
twoArmIf :: Simple -> TwoArmIf
twoArmIf (Simple ir) = TwoArmIf (exp ir)
  where
    exp :: Exp Simple -> Exp TwoArmIf
    exp (If b0 t0 (Just f0))
      = let b = exp b0  -- this part is automatic
            t = exp t0
            f = exp f0
        in If b t f
    exp (If b0 t0 Nothing)
      = let b = exp b0
            t = exp t0
        in If b t (Exp 0)
    -- automatic clauses
    exp (Exp i) = Exp i
    exp (While b e) = While b (exp e)
    exp (Block es)  = Block (map exp es)

The Transform' type is special. It can be defined on the Haskell side
(for purposes of having a defined literal to reference) as a closed type family
with no instances. Or something like that. It doesn't really matter. Maybe as a
type error.

Transform' N M is a processor for nonterminal N that returns nonterminal M.
Transform N a M r is a processor for nonterminal N that additionally takes
  argument a, and returns nonterminal M along with extra result r.

Transform' is N () M (). If a is a tuple it should be curried into the
transformer's arguments. r can't be, for obvious reasons. I'm not quite sure
what to do with that.

Definitions that don't have Transformer type are extra definitions and are
dropped directly into the 'where' block. The documentation should mention that
all definitions have access to the pass argument if they want it.
-}

-- | A newtype (equivalent to Identity) with constructor 'R' used to signal
-- automatic catamorphism in passes. The pattern (R a) in a pass is translated
-- by first recursively applying the pass to 'a' and then binding the identifier
-- 'a' to the result. If 'a' is a more complex pattern, it _must_ be an
-- as-pattern. (R x@p) will match p, recursively apply the pass to the matched
-- value, and then bind the result to 'x'. Other names bound by the pattern
-- will have their original (pre-recursion) values.
--
-- The automatic recurser is smart enough to work through functors, so if the
-- pattern looks like (R f), with f :: Maybe Exp, then a transformer of type
-- Exp -> Exp can be selected and used via fmap.
--
-- View pattern syntax can be used to also specify the transformer to recurse
-- with; (R (tr -> p)) behaves like (R p) but uses transformer tr instead of trying
-- to select one automatically. This requires the ViewPatterns extension to be
-- enabled.
data Recurse = R

-- plan: support no-nonterminal contexts by using an explicit () for n or m
-- | These definitions are to be considered synthetic; this is _not_ what
-- the types actually mean in a pass, although it is a close approximation.
type Transform n a m r = a -> n -> (r, m)
type Transform' n m = Transform n () m ()

pattern TransformTy :: Type -> Type -> Type -> Type -> Type
pattern TransformTy n a m r <- 
  AppT 
    (AppT
      (AppT
        (AppT ((ConT ''Transform ==) -> True)
              n) a) m) r
  where
    TransformTy n a m r = AppT (AppT (AppT (AppT (ConT ''Transform) n) a) m) r

pattern Transform'Ty :: Type -> Type -> Type
pattern Transform'Ty n m <- AppT (AppT ((ConT ''Transform' ==) -> True) n) m
  where
    Transform'Ty n m = AppT (AppT (ConT ''Transform') n) m

pattern TwoArgFunTy :: Type -> Type -> Type
pattern TwoArgFunTy ty1 ty2 = AppT (AppT ArrowT ty1) ty2

definePass :: Q [Dec] -> Q [Dec]
definePass x = x >>= processPass

processPass :: [Dec] -> Q [Dec]
processPass [] = fail "definePass: no definitions"
processPass
  decs@(SigD passName
             (TwoArgFunTy (ConT leftLangName) (ConT rightLangName))
  : defns
  ) = do
  mleftLang  <- lookupLanguage leftLangName
  mrightLang <- lookupLanguage rightLangName
  (leftLang, rightLang) <- case (mleftLang, mrightLang) of
    (Just l, Just r) -> pure (l,r)
    _ -> fail $ failMsg mleftLang mrightLang
  let cxt = PassContext passName leftLang rightLang
  processAllPassDecs cxt decs
  where
    failMsg ml mr = "Couldn't find representation"
                  ++ midPart ml mr ++ " needed for pass definition."
      where leftN  = "`" ++ show leftLangName  ++ "'"
            rightN = "`" ++ show rightLangName ++ "'"
            midPart Nothing Nothing = "s for either " ++ leftN ++ " or " ++ rightN
            midPart Nothing Just{}  = " for " ++ leftN
            midPart Just{}  Nothing = " for " ++ rightN
            midPart Just{}  Just{}  = error "unreachable"
processPass _ = fail "definePass: first declaration must be the pass type signature."

-------------------------------------------------------------------------------
-- Pass-contextual rewriting
-------------------------------------------------------------------------------

data PassContext = PassContext
  { passName :: Name
  , inLang   :: LanguageRep
  , outLang  :: LanguageRep
  }

processAllPassDecs :: PassContext -> [Dec] -> Q [Dec]
processAllPassDecs cxt decs = do
  passDef' <- processPassDef cxt passDef
  localDefs' <- rewriteDefs cxt localDefs
  let passDef'' = moveToLocalOf passDef' localDefs'
  return $ defDecs passDef''
  where
    ([passDef], localDefs) = partition ((== passName cxt) . defName) oneDefs
    oneDefs = breakDefs decs

-- For now we are assuming the entire pass is given, so there's nothing to do here.
processPassDef :: PassContext -> OneDef -> Q OneDef
processPassDef _ = pure

-- we should try and do better than this in the future, by using some synthetic
-- intermediate value so that all of the decs can share the locals.
-- That would also let the FunD clauses share them automatically :)
moveToLocalOf :: OneDef -> [OneDef] -> OneDef
moveToLocalOf (OneDef n gbl) lcls = OneDef n $ map (addLocals lcls) gbl

addLocals :: [OneDef] -> Dec -> Dec
addLocals lcls (ValD p b olds) = ValD p b (olds ++ mergeDefs lcls)
addLocals lcls (FunD n clauses) = FunD n $ map addToClause clauses
  where
    addToClause (Clause ps b ds) = Clause ps b (ds ++ mergeDefs lcls)
addLocals _ d = d

quoteTransformerPat :: PassContext -> Pat -> Q (Pat, [(Name,Exp)])
quoteTransformerPat cxt pat = do
  pat' <- quote (inLang cxt) pat
  catamorph pat'

quoteTransformerBody :: PassContext -> Body -> Q Body
quoteTransformerBody cxt = quote $ outLang cxt

quoteTransformerType :: PassContext -> Transformer -> Q Type
quoteTransformerType cxt
  Transformer { tSrcNt, tExtraArgs, tOutNt, tExtraRets }
  = foldFunTy <$> traverse (quote $ inLang cxt) (ConT tSrcNt : tExtraArgs)
              <*> quote (outLang cxt) (mkRetTy tOutNt tExtraRets)

-- Doing this for now, but maybe a different default behavior would be better?
-- also what about nested transformers? Allowed or no? Currently not.
quoteTransformerDecs :: PassContext -> [Dec] -> Q [Dec]
quoteTransformerDecs cxt = traverse $ quote $ outLang cxt

quoteTransformerClauses :: PassContext -> [Clause] -> Q [Clause]
quoteTransformerClauses cxt = traverse (quoteTransformerClause cxt)

quoteTransformerClause :: PassContext -> Clause -> Q Clause
quoteTransformerClause cxt (Clause pats body decs) = do
  patsAndCats <- traverse (quoteTransformerPat cxt) pats
  let (pats, concat -> cats) = unzip patsAndCats
  Clause pats <$> quoteTransformerBody cxt body
              <*> ((map mkDec cats ++) <$> quoteTransformerDecs cxt decs)
  where
    mkDec (n,e) = ValD (VarP n) (NormalB e) []

rewriteDefs :: PassContext -> [OneDef] -> Q [OneDef]
rewriteDefs cxt = traverse (rewriteDef cxt) . attachTransformerInfo

rewriteDef :: PassContext -> (OneDef, Maybe Transformer) -> Q OneDef
rewriteDef cxt (od@(OneDef n decs), Nothing) = pure od
rewriteDef cxt (OneDef n decs, Just t) = OneDef n <$> rewriteTransformerDecs cxt t decs

rewriteTransformerDecs :: PassContext -> Transformer -> [Dec] -> Q [Dec]
rewriteTransformerDecs cxt t = traverse $ rewriteTransformerDec cxt t

rewriteTransformerDec :: PassContext -> Transformer -> Dec -> Q Dec
rewriteTransformerDec cxt t = rewriteTransformerSig cxt t >=> rewriteDefD cxt

rewriteTransformerSig :: PassContext -> Transformer -> Dec -> Q Dec
rewriteTransformerSig cxt t SigD{} = SigD (tName t) <$> quoteTransformerType cxt t
rewriteTransformerSig _ _ d = pure d

rewriteDefD :: PassContext -> Dec -> Q Dec
rewriteDefD cxt (ValD pat body decs) = do
  Clause [pat'] body' decs' <- quoteTransformerClause cxt $ Clause [pat] body decs
  return $ ValD pat' body' decs'
rewriteDefD cxt (FunD n clauses)
  = FunD n <$> quoteTransformerClauses cxt clauses
rewriteDefD _ other = pure other

-- returns bindings to be made in a (Name,Exp) pair so that we can handle the
-- monadic and non-monadic cases separately. In the non-monadic case, we want
-- to make the bindings available in guards, so we need them in 'where' bindings.
-- But in the monadic case, they need to be bound by >>=.
--
-- All catamorphism patterns must be in explicit form (view pattern syntax).
catamorph :: Pat -> Q (Pat, [(Name, Exp)])
catamorph p = do 
  (p', ds) <- W.runWriterT (catamorphM p)
  return (p', DL.toList ds)
  where
    catamorphM :: Pat -> W.WriterT (DL.DList (Name,Exp)) Q Pat
    catamorphM p = case p of
      LitP lit             -> pure $ LitP lit
      VarP na              -> pure $ VarP na
      TupP pats            -> TupP <$> traverse go pats
      UnboxedTupP pats     -> UnboxedTupP <$> traverse go pats
      UnboxedSumP pat n i  -> (\p' -> UnboxedSumP p' n i) <$> go pat
      origp@(ConP ((== 'R) -> True) pats)
        | [ViewP tr p] <- pats
        , acceptable p
        -> do (origName, patName) <- namesFor p
              emit origName $ AppE tr (VarE patName)
              let p' = renamePat patName p
              return p'
        | otherwise        -> do W.lift $ reportError "Illegal use of R pattern"
                                 return origp
      ConP na pats         -> ConP na <$> traverse go pats
      InfixP pat1 na pat2  -> InfixP <$> go pat1 <*> pure na <*> go pat2
      UInfixP pat1 na pat2 -> UInfixP <$> go pat1 <*> pure na <*> go pat2
      ParensP pat          -> ParensP <$> go pat
      TildeP pat           -> TildeP <$> go pat
      BangP pat            -> BangP <$> go pat
      AsP na pat           -> AsP na <$> go pat
      WildP                -> pure WildP
      RecP na fps          -> RecP na <$> traverse goFP fps
      ListP pats           -> ListP <$> traverse go pats
      SigP pat ty          -> SigP <$> go pat <*> pure ty
      ViewP exp pat        -> ViewP exp <$> go pat
      where
        go = catamorphM
        goFP (n,p) = (n,) <$> go p

        acceptable :: Pat -> Bool
        acceptable VarP{} = True
        acceptable AsP{}  = True
        acceptable _ = False

        renamePat :: Name -> Pat -> Pat
        renamePat n VarP{}    = VarP n
        renamePat n (AsP _ p) = AsP n p
        renamePat _ _ = error "catamorph.subPat: unacceptable pattern"

        namesFor :: Monoid w => Pat -> W.WriterT w Q (Name, Name)
        namesFor (VarP n)  = W.lift $ (n,) <$> newName (nameBase n)
        namesFor (AsP n _) = W.lift $ (n,) <$> newName (nameBase n)
        namesFor _ = error "catamorph.namesFor: unacceptable pattern"

    emit :: Name -> Exp -> W.WriterT (DL.DList (Name,Exp)) Q ()
    emit n e = W.tell $ DL.singleton (n,e)

foldFunTy :: [Type] -> Type -> Type
foldFunTy tys r = foldr1 TwoArgFunTy (tys ++ [r])

mkRetTy :: Name -> [Type] -> Type
mkRetTy nt extras = foldl AppT (TupleT size) (extras ++ [ConT nt])
  where size = length extras + 1

-------------------------------------------------------------------------------
-- Pass Semantic discovery
-------------------------------------------------------------------------------

data OneDef = OneDef !Name [Dec]

breakDefs :: [Dec] -> [OneDef]
breakDefs decs = map (decName . head >>= OneDef)
               $ groupOn decName $ sortOn decName decs

mergeDefs :: [OneDef] -> [Dec]
mergeDefs = (>>= defDecs)

defName :: OneDef -> Name
defName (OneDef n _) = n

defDecs :: OneDef -> [Dec]
defDecs (OneDef _ decs) = decs

type NtName = Name
data Transformer = Transformer
  { tName  :: Name
  -- eventually: Maybe NtNames (no-nonterminal contexts)
  , tSrcNt :: NtName
  , tOutNt :: NtName
  -- we will only autogenerate transformers with no extra arguments or returns
  -- but we _will_ sometimes select transformers that don't: while generating
  -- clauses we will match the extra{args,rets} of the containing processor.
  -- We will select a transformer if and only if the extras match exactly;
  -- we could probably be a smarter by using meta names again but I'm not sure
  -- exactly how that would work so we'll leave it for later.
  , tExtraArgs :: [Type]
  , tExtraRets :: [Type]
  -- , tMonad :: Maybe Type
  }

gatherTransformerInfo :: [OneDef] -> [Transformer]
gatherTransformerInfo = mapMaybe defTransformerInfo

attachTransformerInfo :: [OneDef] -> [(OneDef, Maybe Transformer)]
attachTransformerInfo = map $ mapToSnd defTransformerInfo
  where mapToSnd f x = (x, f x)

defTransformerInfo :: OneDef -> Maybe Transformer
defTransformerInfo (OneDef name decs) = do
  SigD _n transType <- findDecsTySig decs
  case transType of
    Transform'Ty (ConT snt) (ConT ont) ->
      Just $ Transformer{ tName = name
                        , tSrcNt = snt, tOutNt = ont
                        , tExtraArgs = [], tExtraRets = []
                        }
    TransformTy (ConT snt) (unfoldTupleT -> Just atys)
                (ConT ont) (unfoldTupleT -> Just rtys) ->
      Just $ Transformer{ tName = name
                        , tSrcNt = snt, tOutNt = ont
                        , tExtraArgs = atys, tExtraRets = rtys
                        }
    _ -> Nothing

decName :: Dec -> Name
decName (SigD n _) = n
decName (ValD (VarP n) _ _) = n
decName (FunD n _) = n
decName (InfixD _ n) = n
-- any other declaration is something that we should still LangQuote & splice
-- back, but it's not something that needs to be processed and moved up into
-- the local bindings of the pass. We want them all grouped together so that
-- we can just copy them into the output, but that's about it.
-- We use a capitalized name here to avoid capture.
decName _ = mkName "Anonymous_declaration"

findDecsTySig :: [Dec] -> Maybe Dec
findDecsTySig [] = Nothing
findDecsTySig (d@SigD{} : _) = Just d
findDecsTySig (_ : ds) = findDecsTySig ds

groupOn :: Eq a => (b -> a) -> [b] -> [[b]]
groupOn f = groupBy (\x y -> f x == f y)

unfoldTupleT :: Type -> Maybe [Type]
unfoldTupleT ty = case split ty of
  (TupleT n, tys) | n == length tys -> Just tys
  _ -> Nothing
