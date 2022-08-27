{-# LANGUAGE NamedFieldPuns, TupleSections, LambdaCase #-}
{-# LANGUAGE TypeFamilies, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
module TH.DefineLanguage where

import TH.LanguageFamilyRepr
import qualified TH.LinguistRegistry as Registry

import Text.Parsec hiding (State, parse)
import qualified Text.Parsec as P (parse)
import Text.Parsec.Char
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Quote as TH

import Data.Coerce (coerce)
import qualified Data.List as L
import Data.Function ((&))
import Data.Functor (($>))
import Data.Functor.Identity
import Data.Bifunctor (second)
import qualified Data.Graph as G
import qualified Data.HashMap.Lazy as H
import qualified Data.HashSet as S
import Data.Hashable (Hashable(..))
import Data.IORef
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Any(..))
import Data.Char (isUpper, isLower)
import Data.Void (Void, absurd)
import Control.Monad (guard, void, foldM, unless, mplus)
import Control.Monad.State
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import Control.Monad.Writer

import Debug.Trace
import Text.Pretty.Simple
import Control.Monad.Reader

-------------------------------------------------------------------------------
-- Try to parse the damn thing
--
-- This is really just a prototype and shouldn't be considered final.
-- The general approach here is to over-parse, and parse _deltas_ where
-- we would need to know about the parent language to build the whole Language
-- struct. Then we validate the whole structure that we parse separately.
-- Then we can add all the languages that we found to the map.
-- (We don't want to use the map as an intermediate storage because we don't
-- want to be able to extend languages defined in a different splice - with
-- the encoding we are using now, this would make Bad Things happen.)
--
-- Someday we'd like indentation sensitivity.
-------------------------------------------------------------------------------

type Parser = Parsec String ()

parse :: String -> TH.Q [Rdr ParsedLanguage]
parse inp = do
  loc <- TH.location
  let r = P.parse (parser loc) (TH.loc_filename loc) inp
  case r of
    Left e  -> fail $ show e
    Right v -> return v
  where
    parser loc = do
      pos <- getPosition
      let (line,col) = TH.loc_start loc
          pos'  = setSourceLine pos line
          pos'' = setSourceColumn pos' col
      setPosition pos''
      whiteSpace *>  many1 parseLanguage <* eof

style :: LanguageDef ()
style = haskellStyle
  { Token.reservedOpNames = ["::", "=", "+", "-", "+=", "-=", "|", ";"]
  , Token.reservedNames = ["language", "where", "extends", "entry", "terminals"]
  }

lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser style

parens :: Parser a -> Parser a
parens = Token.parens lexer

brackets :: Parser a -> Parser a
brackets = Token.brackets lexer

reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

reserved :: String -> Parser ()
reserved = Token.reserved lexer

commaSep1 :: Parser a -> Parser [a]
commaSep1 = Token.commaSep1 lexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

nameParser :: String -> Parser a -> Parser a
nameParser = flip label

bigIdent :: Parser BigName
bigIdent = nameParser "uppercase identifier" $ try $ do
  ident <- Token.identifier lexer
  guard $ isUpper $ head ident
  return $ BigName ident

smallIdent :: Parser SmallName
smallIdent = nameParser "lowercase identifier" $ try $ do
  ident <- Token.identifier lexer
  guard $ isLower $ head ident
  return $ SmallName ident

type Rdr f = f BigName SmallName
data ParsedLanguage nameTy eltTy
  = BaseLanguage (Language nameTy eltTy)
  | Extension    (LanguageDelta nameTy eltTy)

deriving instance
  ( Show (Language nameTy eltTy)
  , Show (LanguageDelta nameTy eltTy)
  ) => Show (ParsedLanguage nameTy eltTy)

parseLanguage :: Parser (Rdr ParsedLanguage)
parseLanguage = nameParser "language definition" $ do
  reserved "language"
  name <- bigIdent
  reserved "where"
  mextends <- optionMaybe parseExtendsClause
  case mextends of
    Nothing -> BaseLanguage <$> parseBaseLanguage name
    Just s  -> Extension <$> s `parseExtensionOf` name

parseExtendsClause :: Parser BigName
parseExtendsClause = nameParser "extends clause" $ do
  reserved "extends"
  bigIdent

parseEntryClause :: Parser BigName
parseEntryClause = nameParser "entry clause" $ do
  reserved "entry"
  bigIdent

parseBaseLanguage :: BigName -> Parser (Rdr Language)
parseBaseLanguage name = do
  mEntry <- optionMaybe parseEntryClause
  terminals <- parseTerminalClause
  (nonterminals, ntTags, fstNtName) <- parseNonterminals
  return $ Language
    { langName          = name
    , langEntry         = fromMaybe fstNtName mEntry
    , langTerminals     = terminals
    , langNonterminalMC = ntTags
    , langNonterminals  = nonterminals
    --, langDelta         = Nothing
    }

parseExtensionOf :: BigName -> BigName -> Parser (Rdr LanguageDelta)
parseExtensionOf base name = do
  mEntry <- optionMaybe parseEntryClause
  td <- parseTerminalExtensionClause <?> "terminal extension clause"
  ntd <- parseNonterminalExtensionClauses <?> "nonterminal extension clause"
  return $ LanguageDelta
    { extensionName    = name
    , sourceLanguage   = base
    , newLangEntry     = mEntry
    , terminalDelta    = td
    , nonterminalDelta = ntd
    }

parseTerminalClause :: Parser [(SmallName, Rdr Terminal)]
parseTerminalClause = do
  reserved "terminals"
  parseTerminals <* reservedOp ";"

parseTerminals :: Parser [(SmallName, Rdr Terminal)]
parseTerminals = do
  terminals <- many1 parseTerminal
  let extractPairing (ns, t) = map (,t) ns
      pairs = terminals >>= extractPairing
  return pairs

parseTerminal :: Parser ([SmallName], Rdr Terminal)
parseTerminal = do
  ns <- commaSep1 smallIdent
  reservedOp "::"
  ty <- bigIdent
  return (ns, Terminal ty ns)

parseTerminalExtensionClause :: Parser (Rdr TerminalDelta)
parseTerminalExtensionClause = fmap finalize $ optionMaybe $ do
  reserved "terminals"
  deleted <- optionMaybe $ do
    reservedOp "-"
    commaSep1 smallIdent
  added <- optionMaybe $ do
    reservedOp "+"
    parseTerminals
  reservedOp ";"
  return $ TerminalDelta
    { removedTerminals = fromMaybe [] deleted
    , addedTerminals   = fromMaybe [] added
    }
  where finalize = fromMaybe (TerminalDelta [] [])

-- | Parse a series of nonterminal clauses. Return a mapping from metanames
-- to nonterminals and also the name of the first nonterminal for entry
-- resolution.
parseNonterminals :: Parser ( H.HashMap BigName (Rdr Nonterminal)
                            , [(SmallName, Rdr NtTag)]
                            , BigName
                            )
parseNonterminals = do
  nts <- many1 parseNonterminal
  let extractPairing p@(nt, ns) = map (,NtTag $ nonterminalName nt) ns
      pairs = nts >>= extractPairing
      ntMapping = H.fromList [ (nonterminalName nt, nt) | (nt,_) <- nts ]
  return (ntMapping, pairs, nonterminalName $ fst $ head nts)

parseNonterminalExtensionClauses
  :: Parser (Rdr NonterminalDelta)
parseNonterminalExtensionClauses = do
  extensions <- many parseNtExtensionClause
  let deleted  = [ n | DeletedNt n <- extensions ]
      added    = [ p | AddedNt p <- extensions ]
      addedTags = [ (n, NtTag (nonterminalName nt)) | (nt,ns) <- added, n <- ns ]
      addedNts = H.fromList [ (nonterminalName nt, nt) | (nt,_) <- added ]
      modified = H.fromList [ (n, nd) | ModifiedNt (n, nd) <- extensions ]
  return $ NonterminalDelta
    { removedNonterminals  = deleted
    , addedNonterminalsMC  = addedTags
    , addedNonterminals    = addedNts
    , modifiedNonterminals = modified
    }

data NonterminalExtension
  = DeletedNt BigName
  | AddedNt (Rdr Nonterminal, [SmallName])
  | ModifiedNt (BigName, Rdr OneNonterminalDelta)

parseNtExtensionClause :: Parser NonterminalExtension
parseNtExtensionClause
  =   DeletedNt  <$> parseDeleteNt
  <|> AddedNt    <$> parseAddedNt
  <|> ModifiedNt <$> parseModifiedNt

parseDeleteNt :: Parser BigName
parseDeleteNt = reservedOp "-" *> bigIdent

parseAddedNt :: Parser (Rdr Nonterminal, [SmallName])
parseAddedNt = reservedOp "+" *> parseNonterminal

parseModifiedNt :: Parser (BigName, Rdr OneNonterminalDelta)
parseModifiedNt = do
  ntName <- bigIdent
  deleteConstrs <- optionMaybe $ do
    reservedOp "-="
    commaSep1 bigIdent
  newConstrs <- optionMaybe $ do
    reservedOp "+="
    parseConstr `sepBy` reservedOp "|"
  reservedOp ";"
  let extractPair nt@(LangConstr n _ _) = (n, nt{constrSrcNt=ntName})
      pairs = maybe [] (map extractPair) newConstrs
  return (ntName, OneNonterminalDelta
    { removedConstrs = fromMaybe [] deleteConstrs
    , addedConstrs  = H.fromList pairs
    })

parseNonterminal :: Parser (Rdr Nonterminal, [SmallName])
parseNonterminal = do
  metaNames <- commaSep1 smallIdent
  reservedOp "::"
  ntName <- bigIdent
  reservedOp "="
  constrs <- parseConstr `sepBy` reservedOp "|"
  reservedOp ";" -- unfortunate but seems necessary for no lookahead
  let extractPair nt@(LangConstr n _ _) = (n, nt{constrSrcNt=ntName})
      pairs = map extractPair constrs
  return (Nonterminal ntName (H.fromList pairs) metaNames, metaNames)

parseConstr :: Parser (Rdr LangConstr)
parseConstr = LangConstr <$> bigIdent <*> pure undefined <*> many parseBaseElt

parseBaseElt :: Parser (Rdr ConstrElt)
parseBaseElt = (PureElt <$> smallIdent) <|> parens parseConstrElt <|> parseListElt

parseListElt :: Parser (Rdr ConstrElt)
parseListElt = brackets $ ListElt <$> (parseArbitrary <|> parseOne)
  where
    parseOne = fmap (:[]) parseConstrElt
    parseArbitrary = parens $ commaSep1 parseConstrElt

parseAppElt :: Parser (Rdr ConstrElt)
parseAppElt = AppElt <$> (bigIdent <?> "functor name") <*> parseBaseElt

parseConstrElt :: Parser (Rdr ConstrElt)
parseConstrElt = parseBaseElt <|> parseAppElt <?> "constructor element"

-------------------------------------------------------------------------------
-- Re-order the parsed family using a graph for validation
-------------------------------------------------------------------------------

type NodeFromVertex = G.Vertex -> (Rdr ParsedLanguage, BigName, [BigName])
type VertexFromKey  = BigName -> Maybe G.Vertex

topSortLangFam :: [Rdr ParsedLanguage] -> [Rdr ParsedLanguage]
topSortLangFam langs = map (extract . nFromV) sorted
  where
    (inherits, nFromV, vFromK) = G.graphFromEdges $ map mkEdges langs
    super = G.transposeG inherits
    sorted = G.topSort super
    mkEdges pl@(BaseLanguage lang) = (pl, langName lang, [])
    mkEdges pl@(Extension elang) = (pl, extensionName elang, [sourceLanguage elang])
    extract (thing,_,_) = thing

-------------------------------------------------------------------------------
-- Do some validation
--
-- (1) no duplicated metanames
-- (2) deleted terms/nts/constrs existed before
-- (3) added terms/nts/constrs _didn't_ exist before
--       it's surprisingly difficult to check this for nonterminals
--       Perhaps the parsed nonterminals should come out in groups...
--       unsurprisingly I feel like it would be easier to dogfood, lol.
--
-- We only want to check the things that can't be checked by GHC after
-- we desugar the language definitions to TH source. That mostly means
-- checking that doing the prescribed modifications to the internal rep
-- won't cause accidental loss of information.
-- If we wanted to emit warnings, we should do it here too.
-------------------------------------------------------------------------------

validateLangFam :: [Rdr ParsedLanguage] -> TH.Q [Vld ParsedLanguage]
validateLangFam langs = evalStateT (validateLangFam' langs) mempty

type NtName     = BigName
type ConstrName = BigName

type ValidateCxt
  = H.HashMap BigName
                ( S.HashSet MetaName
                , H.HashMap NtName [MetaName]
                , S.HashSet ConstrName
                )

type Vld f = f BigName MetaName

validateLangFam' :: [Rdr ParsedLanguage]
                 -> StateT ValidateCxt TH.Q [Vld ParsedLanguage]
validateLangFam' = traverse validateLang

validateLang :: Rdr ParsedLanguage -> StateT ValidateCxt TH.Q (Vld ParsedLanguage)
validateLang pl = case pl of
  BaseLanguage lang -> BaseLanguage <$> validateBaseLang lang
  Extension elang   -> Extension <$> validateExtension elang

validateBaseLang :: Rdr Language -> StateT ValidateCxt TH.Q (Vld Language)
validateBaseLang lang = do
  lift $ validateTerminalDups $ map fst $ langTerminals lang
  lift $ validateNtDups $ map fst $ langNonterminalMC lang
  let vldTerminals = metaifyTerms $ langTerminals lang
      vldNtTags = metaifyNtTags $ langNonterminalMC lang
      vldNts = metaifyNts $ langNonterminals lang
      doubledMns = H.intersection vldTerminals vldNtTags
  lift $ validateDoubledMns doubledMns
  let metanames = S.fromList $ H.keys $ H.union (vldTerminals $> ()) (vldNtTags $> ())
      ntnames     = vldNtTags & fmap getNtTag & H.toList
                  & map (\(a,b) -> (b, [a])) & H.fromListWith (++)
      constrnames = vldNts & H.elems & map nonterminalConstrs
                  & H.unions & H.keys & S.fromList
      newCxt = (metanames, ntnames, constrnames)
  modify $ H.insert (langName lang) newCxt
  return $ Language (langName lang)
                    (langEntry lang)
                    vldTerminals
                    vldNtTags
                    vldNts
                    -- Nothing

validateExtension :: Rdr LanguageDelta -> StateT ValidateCxt TH.Q (Vld LanguageDelta)
validateExtension elang = do
  (baseTCxt, baseNtCxt, baseConstrCxt) <- gets (H.! sourceLanguage elang)
  let td = terminalDelta elang
      rt = removedTerminals td
      at = addedTerminals td
      ntd = nonterminalDelta elang
      rnt = removedNonterminals ntd
      atags = addedNonterminalsMC ntd
      antPairs = map (second getNtTag) atags
  ntCxt <- lift $ validateNtChanges baseNtCxt rnt antPairs
  ctCxt <- lift $ validateConstrChanges baseConstrCxt ntd
  mnCxt <- lift $ validateExtMetas baseTCxt baseNtCxt rt (map fst at) rnt (map fst atags)
  modify $ H.insert (extensionName elang) (mnCxt,ntCxt,ctCxt)
  return $ metaifyLanguageDelta elang

validateTerminalDups :: [SmallName] -> TH.Q ()
validateTerminalDups pairs = mapM_ reportTerminalDup dups
  where grouping = L.group pairs
        dups = map head $ filter (not . null . tail) grouping
        reportTerminalDup sn = TH.reportError $
          "Meta name `" ++ show sn ++ "' given for multiple terminals"

validateExtMetas :: S.HashSet MetaName
                 -> H.HashMap BigName [MetaName]
                 -> [SmallName] -> [SmallName]
                 -> [BigName]   -> [SmallName]
                 -> TH.Q (S.HashSet MetaName)
validateExtMetas baseT baseNt rt at rnt ant = do
  --validateNtChanges runs first so shouldn't be needed
  --validateNtDeletions baseNt rnt
  let deletedMetas = map MetaName rt ++ (rnt >>= extract)
      extract n = fromMaybe [] (baseNt H.!? n)
      addedMetas   = at ++ ant
  validateExtMetaDups baseT deletedMetas addedMetas

validateNtChanges :: H.HashMap BigName [MetaName]
                  -> [BigName]
                  -> [(SmallName, BigName)]
                  -> TH.Q (H.HashMap BigName [MetaName])
validateNtChanges baseNt rnt ant = do
  validateNtDeletions baseNt rnt
  let newMap = ant & map (\(a,b) -> (b, [MetaName a])) & H.fromListWith (++)
  return $ baseNt `H.union` newMap

validateNtDeletions :: H.HashMap BigName [MetaName] -> [BigName] -> TH.Q ()
validateNtDeletions base = mapM_ validateDeletion
  where
    validateDeletion n
      | n `H.member` base = pure ()
      | otherwise = TH.reportWarning $
        "Deleting nonterminal `" ++ show n ++ "', but it isn't present"

validateExtMetaDups :: S.HashSet MetaName -> [MetaName] -> [SmallName]
                    -> TH.Q (S.HashSet MetaName)
validateExtMetaDups base remove add = do
  glb <- validateDeletions base remove
  validateAdditions glb $ map MetaName add
  where
    validateDeletions base remove = foldM tryDelete base remove
    tryDelete base n
      | n `S.member` base = pure $ n `S.delete` base
      | otherwise = do
        TH.reportWarning $
          "Deleting terminal meta name `"
          ++ show n ++ "', but it isn't present in the base language"
        pure base

    validateAdditions base add = foldM tryAdd base add
    tryAdd base n
      | not $ n `S.member` base = pure $ n `S.insert` base
      | otherwise = do
        TH.reportError $ "Meta name `" ++ show n ++ "' is duplicated"
        pure base

validateConstrChanges :: S.HashSet BigName -> Rdr NonterminalDelta
                      -> TH.Q (S.HashSet BigName)
validateConstrChanges base NonterminalDelta{modifiedNonterminals} = do
  let onds = H.elems modifiedNonterminals
      removed = onds >>= removedConstrs
      added = onds >>= H.keys . addedConstrs
  glb <- validateDeletions base removed
  validateAdditions glb added
  where
    validateDeletions base remove = foldM tryDelete base remove
    tryDelete base n
      | n `S.member` base = pure $ n `S.delete` base
      | otherwise = do
        TH.reportWarning $
          "Deleting constructor `"
          ++ show n ++ "', but it isn't present in the base language"
        pure base

    validateAdditions base add = foldM tryAdd base add
    tryAdd base n
      | not $ n `S.member` base = pure $ n `S.insert` base
      | otherwise = do
        TH.reportError $ "Constructor `" ++ show n ++ "' is duplicated"
        pure base


validateNtDups :: [SmallName] -> TH.Q ()
validateNtDups pairs = mapM_ reportNonterminalDup dups
  where grouping = L.group pairs
        dups = map head $ filter (not . null . tail) grouping
        reportNonterminalDup sn = TH.reportError $
          "Meta name `" ++ show sn ++ "' given for multiple nonterminals"

validateDoubledMns :: H.HashMap MetaName a -> TH.Q ()
validateDoubledMns m = do
  mapM_ reportDoubled $ H.keys m
  unless (null m) $ fail "Couldn't validate meta names."

reportDoubled :: MetaName -> TH.Q ()
reportDoubled mn = TH.reportError $
  "Meta name `" ++ show mn ++ "' given for both terminal and nonterminal"

metaifyTerms :: MetaCollection Terminal BigName SmallName
             -> MetaCollection Terminal BigName MetaName
metaifyTerms terms = H.fromList $ map metaifyPair terms
  where
    metaifyPair (sn, t) = (MetaName sn, metaifyTerm t)
    metaifyTerm (Terminal n ns) = Terminal n $ map MetaName ns

metaifyNtTags :: MetaCollection NtTag BigName SmallName
              -> MetaCollection NtTag BigName MetaName
metaifyNtTags tags =
  H.fromList [ (MetaName s, NtTag tag) | (s, NtTag tag) <- tags ]

metaifyNts :: H.HashMap BigName (Rdr Nonterminal)
           -> H.HashMap BigName (Vld Nonterminal)
metaifyNts = fmap metaifyNt

metaifyNt :: Rdr Nonterminal -> Vld Nonterminal
metaifyNt Nonterminal{nonterminalName, nonterminalConstrs, nonterminalMetanames}
  = Nonterminal nonterminalName
                (fmap metaifyLangConstr nonterminalConstrs)
                (fmap MetaName nonterminalMetanames)

metaifyLangConstr :: Rdr LangConstr -> Vld LangConstr
metaifyLangConstr (LangConstr n nt cs) = LangConstr n nt $ map metaifyConstrElt cs

metaifyConstrElt :: Rdr ConstrElt -> Vld ConstrElt
metaifyConstrElt (PureElt sn)  = PureElt (MetaName sn)
metaifyConstrElt (ListElt es)  = ListElt $ map metaifyConstrElt es
metaifyConstrElt (AppElt fn e) = AppElt fn $ metaifyConstrElt e

metaifyLanguageDelta :: Rdr LanguageDelta -> Vld LanguageDelta
metaifyLanguageDelta
  LanguageDelta{ extensionName
               , sourceLanguage
               , newLangEntry
               , terminalDelta
               , nonterminalDelta
               }
    = LanguageDelta extensionName
                    sourceLanguage
                    newLangEntry
                    (metaifyTerminalDelta terminalDelta)
                    (metaifyNonterminalDelta nonterminalDelta)

metaifyTerminalDelta :: Rdr TerminalDelta -> Vld TerminalDelta
metaifyTerminalDelta TerminalDelta{removedTerminals, addedTerminals}
  = TerminalDelta { removedTerminals = map MetaName removedTerminals
                  , addedTerminals = metaifyTerms addedTerminals}

metaifyNonterminalDelta :: Rdr NonterminalDelta -> Vld NonterminalDelta
metaifyNonterminalDelta
  NonterminalDelta{ removedNonterminals
                  , addedNonterminalsMC
                  , addedNonterminals
                  , modifiedNonterminals
                  }
  = NonterminalDelta
    { removedNonterminals
    , addedNonterminalsMC = metaifyNtTags addedNonterminalsMC
    , addedNonterminals = metaifyNts addedNonterminals
    , modifiedNonterminals = fmap metaifyOntd modifiedNonterminals
    }

metaifyOntd :: Rdr OneNonterminalDelta -> Vld OneNonterminalDelta
metaifyOntd OneNonterminalDelta{removedConstrs, addedConstrs}
  = OneNonterminalDelta
    { removedConstrs
    , addedConstrs = fmap metaifyLangConstr addedConstrs
    }

-------------------------------------------------------------------------------
-- resolve big names (so much easier...)
--
-- The goal is to replace BigNames with type/constructor names for
-- TH. If the name is something that should be in scope already (terminal
-- or wrapper) then we should look it up and complain if we can't find it.
-- Otherwise we should make a new name for it.
--
-- If we have to complain because something is out-of-scope, we make our own
-- name for it so that we can keep going. The quasiquoter will fail, so there
-- won't also be scoping errors from the renamer.
-------------------------------------------------------------------------------

resolveB :: [Vld ParsedLanguage] -> TH.Q [Rbn ParsedLanguage]
resolveB pls = do
  mod <- TH.thisModule
  evalStateT (runReaderT (resolveBigNames pls) mod) H.empty

type Rbn f = f TH.Name MetaName

instance Hashable TH.NameSpace
type BigNameMap = H.HashMap (BigName, TH.NameSpace) TH.Name
type ResolveB = ReaderT TH.Module (StateT BigNameMap TH.Q)

liftRB :: TH.Q a -> ResolveB a
liftRB = lift . lift

check :: BigName -> TH.NameSpace -> MaybeT ResolveB TH.Name
check n sp = MaybeT $ gets (H.!? (n,sp))

resolveTerminal :: BigName -> ResolveB TH.Name
resolveTerminal bn@(BigName n) = do
  mthn <- runMaybeT $ check bn TH.TcClsName 
                      `mplus` MaybeT (liftRB (TH.lookupTypeName n))
  case mthn of
    Just thn -> return thn
    Nothing -> do
      liftRB $ TH.reportError $ "Out of scope: terminal type `" ++ n ++ "'"
      let thn = TH.mkName n
      modify $ H.insert (bn,TH.TcClsName) thn
      return thn

resolveWrapper :: BigName -> ResolveB TH.Name
resolveWrapper (BigName n) = do
  mthn <- liftRB $ TH.lookupTypeName n
  case mthn of
    Just thn -> return thn
    Nothing -> do
      liftRB $ TH.reportError $ "Out of scope: wrapper type `" ++ n ++ "'"
      let thn = TH.mkName n
      return thn

resolveOurDataCon, resolveOurType :: BigName -> ResolveB TH.Name
resolveOurDataCon = resolveOurs TH.DataName
resolveOurType    = resolveOurs TH.TcClsName

resolveOurs :: TH.NameSpace -> BigName -> ResolveB TH.Name
resolveOurs sp bn@(BigName n) = runMaybeT (check bn sp) >>= \case
   Just thn -> return thn
   Nothing -> do
     TH.Module (TH.PkgName pkg) (TH.ModName mod) <- ask
     let thn = TH.mkNameG sp pkg mod n
     modify $ H.insert (bn,sp) thn
     return thn

resolveBigNames :: [Vld ParsedLanguage] -> ResolveB [Rbn ParsedLanguage]
resolveBigNames = mapM resolveBigNamesInOne

resolveBigNamesInOne :: Vld ParsedLanguage -> ResolveB (Rbn ParsedLanguage)
resolveBigNamesInOne (BaseLanguage lang)
  = BaseLanguage <$> resolveBigNamesBase lang
resolveBigNamesInOne (Extension elang)
  = Extension <$> resolveBigNamesExt elang

resolveBigNamesBase :: Vld Language -> ResolveB (Rbn Language)
resolveBigNamesBase
  Language{ langName
          , langEntry
          , langTerminals
          , langNonterminalMC
          , langNonterminals
          --, langDelta
          }
  = Language <$> resolveOurType langName
             <*> resolveOurType langEntry
             <*> resolveTerminals langTerminals
             <*> resolveNtTags       langNonterminalMC
             <*> resolveNonterminals langNonterminals
             -- <*> pure Nothing -- always Nothing until buildLangs

resolveBigNamesExt :: Vld LanguageDelta -> ResolveB (Rbn LanguageDelta)
resolveBigNamesExt
  LanguageDelta { extensionName
                , sourceLanguage
                , newLangEntry
                , terminalDelta
                , nonterminalDelta
                }
  = LanguageDelta <$> resolveOurType extensionName
                  <*> resolveOurType sourceLanguage
                  <*> traverse resolveOurType newLangEntry
                  <*> resolveTerminalDelta terminalDelta
                  <*> resolveNonterminalDelta nonterminalDelta

resolveTerminals :: H.HashMap MetaName (Vld Terminal)
                 -> ResolveB (H.HashMap MetaName (Rbn Terminal))
resolveTerminals = traverse resolveTerminalEntity

resolveTerminalEntity :: Vld Terminal -> ResolveB (Rbn Terminal)
resolveTerminalEntity Terminal{terminalTypeName,terminalMetanames}
  = Terminal <$> resolveTerminal terminalTypeName
             <*> pure terminalMetanames

resolveTerminalDelta :: Vld TerminalDelta -> ResolveB (Rbn TerminalDelta)
resolveTerminalDelta TerminalDelta{removedTerminals, addedTerminals}
  = TerminalDelta removedTerminals <$> resolveTerminals addedTerminals

resolveNtTags :: MetaCollection NtTag BigName MetaName
              -> ResolveB (MetaCollection NtTag TH.Name MetaName)
resolveNtTags = traverse resolveNtTag

resolveNtTag :: Vld NtTag -> ResolveB (Rbn NtTag)
resolveNtTag (NtTag bn) = NtTag <$> resolveOurType bn

resolveBNMap :: (Vld f -> ResolveB (Rbn f))
             -> TH.NameSpace
             -> H.HashMap BigName (Vld f)
             -> ResolveB (H.HashMap TH.Name (Rbn f))
resolveBNMap go sp h = do
  h' <- traverse go h
  lift $ gets (\mapping -> H.mapKeys ((mapping H.!) . (,sp)) h')

resolveNonterminals :: H.HashMap BigName (Vld Nonterminal)
                    -> ResolveB (H.HashMap TH.Name (Rbn Nonterminal))
resolveNonterminals = resolveBNMap resolveNonterminal TH.TcClsName

resolveNonterminal :: Vld Nonterminal -> ResolveB (Rbn Nonterminal)
resolveNonterminal Nonterminal{nonterminalName, nonterminalConstrs, nonterminalMetanames}
  = Nonterminal <$> resolveOurType nonterminalName
                <*> resolveConstrs nonterminalConstrs
                <*> pure nonterminalMetanames

resolveNonterminalDelta :: Vld NonterminalDelta -> ResolveB (Rbn NonterminalDelta)
resolveNonterminalDelta
  NonterminalDelta { removedNonterminals
                   , addedNonterminalsMC
                   , addedNonterminals
                   , modifiedNonterminals
                   }
  = NonterminalDelta <$> traverse resolveOurType removedNonterminals
                     <*> resolveNtTags addedNonterminalsMC
                     <*> resolveNonterminals addedNonterminals
                     <*> resolveBNMap resolveOntd TH.TcClsName modifiedNonterminals

resolveConstrs :: H.HashMap BigName (Vld LangConstr)
               -> ResolveB (H.HashMap TH.Name (Rbn LangConstr))
resolveConstrs = resolveBNMap resolveConstr TH.DataName

resolveConstr :: Vld LangConstr -> ResolveB (Rbn LangConstr)
resolveConstr LangConstr{constrName, constrSrcNt, constrContents}
  = LangConstr <$> resolveOurDataCon constrName
               <*> resolveOurType constrSrcNt
               <*> traverse resolveConstrElt constrContents

resolveConstrElt :: Vld ConstrElt -> ResolveB (Rbn ConstrElt)
resolveConstrElt (PureElt e) = pure (PureElt e)
resolveConstrElt (ListElt es) = ListElt <$> traverse resolveConstrElt es
resolveConstrElt (AppElt wrap e)
  = AppElt <$> resolveWrapper wrap <*> resolveConstrElt e

resolveOntd :: Vld OneNonterminalDelta -> ResolveB (Rbn OneNonterminalDelta)
resolveOntd OneNonterminalDelta{removedConstrs,addedConstrs}
  = OneNonterminalDelta <$> traverse resolveOurDataCon removedConstrs
                        <*> resolveConstrs addedConstrs

-------------------------------------------------------------------------------
-- build languages
--
-- Goal is to convert Rbn ParsedLanguage to Rbn Language. That requires
-- constructing Languages from LanguageDeltas.
--
-- We originally wanted to try and collect metadata here about which
-- constructors need HasFamilies or ContentFamilies but it turns out that
-- that metadata requires non-local information (need to know about languages
-- other than the one being processed and the δ) so we split that off into a
-- separate pass post-resolveS which can get more precise info anyway.
-------------------------------------------------------------------------------

buildLanguages :: [Rbn ParsedLanguage] -> [Rbn Language]
buildLanguages pls = evalState (mapM processParsedLanguage pls) emptyBuildState

type LanguageMapping = H.HashMap TH.Name (Rbn Language)

newtype BuildState = BuildState
  { languageMapping :: H.HashMap TH.Name (Rbn Language)
  }
  deriving Show

emptyBuildState :: BuildState
emptyBuildState = BuildState H.empty

type BuildLang = State BuildState

registerBuiltLanguage :: Rbn Language -> BuildLang ()
registerBuiltLanguage l@Language{langName} = modify $ \s@BuildState{languageMapping} ->
  s{languageMapping = H.insert langName l languageMapping}

lookupLanguage :: TH.Name -> BuildLang (Rbn Language)
lookupLanguage n = gets $ \s -> languageMapping s H.! n

processParsedLanguage :: Rbn ParsedLanguage -> BuildLang (Rbn Language)
processParsedLanguage pl = do
  lang <- buildParsedLanguage pl
  registerBuiltLanguage lang
  return lang

buildParsedLanguage :: Rbn ParsedLanguage -> BuildLang (Rbn Language)
buildParsedLanguage (BaseLanguage lang) = pure lang
buildParsedLanguage (Extension elang) = do
  base <- lookupLanguage $ sourceLanguage elang
  let lang = addDelta base elang
  return lang

addDelta :: Rbn Language -> Rbn LanguageDelta -> Rbn Language
addDelta lang δ =
  let Language { langName, langEntry, langTerminals, langNonterminalMC, langNonterminals } = lang
      LanguageDelta
        { extensionName, sourceLanguage, newLangEntry
        , terminalDelta, nonterminalDelta } = δ
      terms = addTerminalDelta langTerminals terminalDelta
      -- for the moment, we're ignoring the problem of redefined terminal types
      -- they need to cause constructors which use them to be marked as needing
      -- a content family. However, I also think that redefining a terminal
      -- should be disallowed in the absence of some kind of "flexible"
      -- annotation on the original terminal.
      tags = addTagDelta langNonterminalMC nonterminalDelta
      nts  = addNonterminalDelta langNonterminals nonterminalDelta
      entry = fromMaybe langEntry newLangEntry
  in Language { langName = extensionName
              , langEntry = entry
              , langTerminals = terms
              , langNonterminalMC = tags
              , langNonterminals = nts
              -- , langDelta = Just δ
              }

-- we've already verified (c.f. phase 2) that the prescribed transformations
-- are valid, so here we just assume it and perform them!
addTerminalDelta :: MetaCollection Terminal TH.Name MetaName
                 -> Rbn TerminalDelta
                 -> MetaCollection Terminal TH.Name MetaName
addTerminalDelta base TerminalDelta{removedTerminals, addedTerminals}
  = addThem $ removeThem base
  where
    removeThem base = foldr H.delete base removedTerminals
    addThem base = base <> addedTerminals

addTagDelta :: MetaCollection NtTag TH.Name MetaName
            -> Rbn NonterminalDelta
            -> MetaCollection NtTag TH.Name MetaName
addTagDelta base NonterminalDelta{removedNonterminals, addedNonterminalsMC}
  = H.filter stays base <> addedNonterminalsMC
  where
    stays (NtTag n) = n `notElem` removedNonterminals

addNonterminalDelta :: H.HashMap TH.Name (Rbn Nonterminal)
                    -> Rbn NonterminalDelta
                    -> H.HashMap TH.Name (Rbn Nonterminal)
addNonterminalDelta base
  NonterminalDelta{ removedNonterminals
                  , addedNonterminals
                  , modifiedNonterminals
                  }
  = modifyNts base modifiedNonterminals
  & removeNts removedNonterminals
  & addNts addedNonterminals
  where
    removeNts ns m = foldr H.delete m ns
    addNts = H.union
    modifyNts m δ = foldr modifyOne m $ H.toList δ
    modifyOne (k,v) = H.adjust (addOntd v) k

addOntd :: Rbn OneNonterminalDelta -> Rbn Nonterminal -> Rbn Nonterminal
addOntd OneNonterminalDelta{removedConstrs, addedConstrs}
        nt@Nonterminal{nonterminalConstrs}
  = nt{nonterminalConstrs =
        foldr H.delete nonterminalConstrs removedConstrs <> addedConstrs
      }

-------------------------------------------------------------------------------
-- Validate metaname uses
--
-- Now that we have explicitly constructed every language, we can check that
-- all meta names used in constructors actually exist. This was possible, but
-- very hard in the first validation phase. However, it's quick and easy now.
-------------------------------------------------------------------------------

validateMetas :: [Rbn Language] -> TH.Q ()
validateMetas = finalize . mapM_ validateMetasOneLang
  where
    finalize w = do
      ((), Any b) <- runWriterT w
      when b $ fail "Couldn't validate metaname uses."

type ValidateMetas = WriterT Any TH.Q

vmReport :: TH.Name -> MetaName -> WriterT Any TH.Q ()
vmReport lang mn = do
  tell $ Any True
  lift $ TH.reportError $ "Invalid usage of metaname `"
                        ++ show mn ++ "' in language `"
                        ++ show lang ++ "'"

validateMetasOneLang :: Rbn Language -> ValidateMetas ()
validateMetasOneLang
  Language { langName
           , langTerminals
           , langNonterminalMC
           , langNonterminals
           }
  = mapM_ validateMetasNt langNonterminals
  where
    metas = H.keysSet langTerminals `S.union` H.keysSet langNonterminalMC
    validateMetasNt = mapM_ validateMetasConstr . nonterminalConstrs
    validateMetasConstr = mapM_ validateMetasConstrElt . constrContents
    validateMetasConstrElt = work
    work (PureElt m) = check m
    work (ListElt es) = mapM_ work es
    work (AppElt w e) = work e

    check n = unless (n `S.member` metas) $ vmReport langName n

-------------------------------------------------------------------------------
-- resolveS : replace MetaNames with TH.Types - a major step!
-------------------------------------------------------------------------------

resolveS :: [Rbn Language] -> [Fin Language]
resolveS = map resolveSLang

resolveSLang :: Rbn Language -> Fin Language
resolveSLang 
  l@Language{langName, langTerminals, langNonterminalMC, langNonterminals}
  = l { langTerminals = resolveSTerminals langTerminals
      , langNonterminalMC = resolveSTags langNonterminalMC
      , langNonterminals = resolveSNts mapping langNonterminals
      }
  where
    termMapping = TH.ConT . terminalTypeName <$> langTerminals
    ntMapping = ntType . getNtTag <$> langNonterminalMC
    mapping = termMapping <> ntMapping

resolveSTerminals :: MetaCollection Terminal TH.Name MetaName
                  -> MetaCollection Terminal TH.Name (MetaName,TH.Type)
resolveSTerminals = H.elems . fmap resolveSTerminal 
  where
    resolveSTerminal (Terminal n mns) = Terminal n mns

resolveSTags :: MetaCollection NtTag TH.Name MetaName
             -> MetaCollection NtTag TH.Name (MetaName,TH.Type)
resolveSTags = coerce . H.elems

resolveSNts :: H.HashMap MetaName TH.Type
            -> H.HashMap TH.Name (Rbn Nonterminal)
            -> H.HashMap TH.Name (Fin Nonterminal)
resolveSNts mapping = fmap (resolveSNt mapping)

resolveSNt :: H.HashMap MetaName TH.Type -> Rbn Nonterminal -> Fin Nonterminal
resolveSNt mapping nt@Nonterminal{nonterminalConstrs, nonterminalMetanames}
  = nt { nonterminalConstrs = fmap (resolveSConstr mapping) nonterminalConstrs
       , nonterminalMetanames
       }

resolveSConstr :: H.HashMap MetaName TH.Type
               -> Rbn LangConstr -> Fin LangConstr
resolveSConstr mapping c@LangConstr{constrContents}
  = c{constrContents = map (resolveSConstrElt mapping) constrContents}

resolveSConstrElt :: H.HashMap MetaName TH.Type
                  -> Rbn ConstrElt -> Fin ConstrElt
resolveSConstrElt mapping = go
  where
    go (PureElt e) = PureElt (e, mapping H.! e)
    go (ListElt es) = ListElt $ map go es
    go (AppElt n e) = AppElt n $ go e

-------------------------------------------------------------------------------
-- Collect family data
--
-- Goal is to, for all constructors, decide which languages they are present in,
-- and conclude their content family equations. If all of the equations are
-- equal, we don't use a content family at all.
--
-- There is no language transformation occurring here.
--
-- The gathered content family will have an eqn with RHS of () if a constr has
-- no contents at that language. If it always has no contents, the family gets
-- tossed and 'represent' will elect to use EmptyConstr.
-------------------------------------------------------------------------------

collectFamilyData :: [Fin Language] -> FamilyData
collectFamilyData langs = FamilyData hasData constrData
  where
    hasData = cleanUpHasData langs $ getAllHasData langs
    constrData = cleanUpContentEqns $ getAllContentEqns langs

type HasFamilyData = H.HashMap TH.Name [LanguageTag]
type ConstrRepData
  = H.HashMap
      TH.Name 
      (Either ConstrContents [(LanguageTag,ContentType)])
type ContentEqns   = H.HashMap TH.Name [(LanguageTag,ContentType)]

data FamilyData = FamilyData
  { hasFamilyData :: HasFamilyData
  , constrRepData :: ConstrRepData
  }

insertOneToListMap :: (Eq k, Hashable k)
                   => k -> v -> H.HashMap k [v] -> H.HashMap k [v]
insertOneToListMap k v = H.alter (Just . (v:) . fromMaybe[]) k

insertHasTag :: TH.Name -> LanguageTag -> HasFamilyData -> HasFamilyData
insertHasTag = insertOneToListMap

insertContentEqn :: TH.Name -> (LanguageTag, ContentType)
                 -> ContentEqns -> ContentEqns
insertContentEqn = insertOneToListMap

getAllHasData :: [Fin Language] -> HasFamilyData
getAllHasData = foldr addLangHasData H.empty

addLangHasData :: Fin Language -> HasFamilyData -> HasFamilyData
addLangHasData Language{langName,langNonterminals} d
  = foldr (addNtHasData langName) d langNonterminals

addNtHasData :: LanguageTag -> Fin Nonterminal -> HasFamilyData -> HasFamilyData
addNtHasData tag Nonterminal{nonterminalConstrs} d
  = foldr (`insertHasTag` tag) d $ H.keys nonterminalConstrs

-- frequently, the data here says that "every language has this constr"
-- in those cases, we really want to just trash the family for that constr
-- because... it doesn't convey anything.
cleanUpHasData :: [Fin Language] -> HasFamilyData -> HasFamilyData
cleanUpHasData langs = H.filterWithKey (\k v -> L.sort (allTags k) /= L.sort v)
  where
    allTags n = map langName $ filter (hasNt n) langs
    hasNt n Language{langNonterminals}
      = (allConstrNts H.! n) `H.member` langNonterminals

    allConstrNts = H.unions $ map findConstrNts langs
    findConstrNts lang
      = invert (H.keysSet . nonterminalConstrs <$> langNonterminals lang)
    invert m = H.fromList [ (v,k) | (k,vs) <- H.toList m, v <- S.toList vs ]

getAllContentEqns :: [Fin Language] -> ContentEqns
getAllContentEqns = foldr addLangContentEqns H.empty

addLangContentEqns :: Fin Language -> ContentEqns -> ContentEqns
addLangContentEqns Language{langName,langNonterminals} eqns
  = foldr (addNtContentEqns langName) eqns langNonterminals

addNtContentEqns :: LanguageTag -> Fin Nonterminal -> ContentEqns -> ContentEqns
addNtContentEqns tag Nonterminal{nonterminalConstrs} d
  = foldr (addConstrContentEqn tag) d $ H.elems nonterminalConstrs

addConstrContentEqn :: LanguageTag -> Fin LangConstr
                    -> ContentEqns -> ContentEqns
addConstrContentEqn tag LangConstr{constrName,constrContents}
  = insertContentEqn constrName (tag, contentTypeOf constrContents)
  where
    contentTypeOf [] = SingleContent unitType
    contentTypeOf [elt] = SingleContent $ thTypeOf elt
    contentTypeOf es = TupleContent $ map thTypeOf es

    thTypeOf (PureElt ty) = snd ty
    thTypeOf (ListElt tys)
      = listType $ foldl1 TH.AppT (TH.TupleT (length tys) : thtys)
      where thtys = map thTypeOf tys
    thTypeOf (AppElt w e) = TH.AppT (TH.ConT w) (thTypeOf e)

cleanUpContentEqns :: ContentEqns -> ConstrRepData
cleanUpContentEqns = fmap cleanUpContentFam

cleanUpContentFam :: [(LanguageTag,ContentType)]
                  -> Either ConstrContents [(LanguageTag,ContentType)]
cleanUpContentFam [] = error "Constructor with no content equations"
cleanUpContentFam eqns@(eqn:_)
  | allEql $ map snd eqns = Left $ reprEqn eqn
  | otherwise = Right $ map fixNtTypesCType eqns
  where
    reprEqn (_,c) = reprCType c
    reprCType (SingleContent (TH.TupleT 0)) = EmptyConstr
    reprCType other = UnchangingConstr other

    fixNtTypesCType :: (LanguageTag,ContentType) -> (LanguageTag,ContentType)
    fixNtTypesCType (tag,SingleContent ty)
      = (tag, SingleContent $ fixNtTypes tag ty)
    fixNtTypesCType (tag,TupleContent tys)
      = (tag, TupleContent $ map (fixNtTypes tag) tys)

    fixNtTypes :: LanguageTag -> TH.Type -> TH.Type
    fixNtTypes tag (TH.AppT tyc a)
      | a == TH.VarT lang = TH.AppT tyc (TH.ConT tag)
      | otherwise = TH.AppT (fixNtTypes tag tyc) (fixNtTypes tag a)
    fixNtTypes _ ty = ty

allEql :: Eq a => [a] -> Bool
allEql [] = True
allEql (hd:tl) = all (== hd) tl

-------------------------------------------------------------------------------
-- represent
--
-- Construct the language family representation
-------------------------------------------------------------------------------

represent :: [Fin Language] -> FamilyData -> LanguageFamilyRepr
represent langs fd =
  LFR { lfrTagsAndEntryNTs = representTagsAndEntries langs
      , lfrNonterminals    = representNonterminals langs fd
      , lfrHasFamilies     = representHasFamilies fd
      , lfrContentFamilies = representContentFamilies fd
      }

representTagsAndEntries :: [Fin Language] -> [(LanguageTag, TH.Name)]
representTagsAndEntries = map repr
  where
    repr Language{langName, langEntry} = (langName, langEntry)

representNonterminals :: [Fin Language] -> FamilyData -> [NonterminalRepr]
representNonterminals langs fd
  = map (representNonterminal fd) $ collectNonterminals langs

representHasFamilies :: FamilyData -> [HasFamily]
representHasFamilies FamilyData{hasFamilyData} = map repr $ H.toList hasFamilyData
  where
    repr (conName, tags) = HasFamily (mkHasFamilyName conName) tags

representContentFamilies :: FamilyData -> [ContentFamily]
representContentFamilies FamilyData{constrRepData}
  = map repr $ [ (n,eqns) | (n, Right eqns) <- H.toList constrRepData ]
  where
    repr (conName,eqns) = ContentFamily (mkContentFamilyName conName) eqns

representNonterminal :: FamilyData -> (TH.Name,[TH.Name]) -> NonterminalRepr
representNonterminal fd (ntName,conNames)
  = NR{ nrName = ntName, nrConstrs = map (representConstr fd) conNames }

representConstr :: FamilyData -> TH.Name -> ConstrRepr
representConstr fd@FamilyData{hasFamilyData,constrRepData} conName
  = CR { crName = conName
       , crHasFamily = hasFamilyData H.!? conName $> mkHasFamilyName conName
       , crContent = reprContent $ constrRepData H.! conName
       }
  where
    reprContent (Left c) = c
    reprContent (Right _eqns) = FamilyConstr $ mkContentFamilyName conName

collectNonterminals :: [Fin Language] -> [(TH.Name,[TH.Name])]
collectNonterminals langs = H.toList $ S.toList <$> collect langs
  where
    -- map nonterminal names to a set of constructor names
    collect :: [Fin Language] -> H.HashMap TH.Name (S.HashSet TH.Name)
    collect = foldr (joinMap . collectOne) H.empty

    collectOne Language{langNonterminals}
      = H.keysSet . nonterminalConstrs <$> langNonterminals

    joinMap = H.unionWith S.union

mkHasFamilyName :: TH.Name -> TH.Name
mkHasFamilyName n = TH.mkName $ "Has" ++ TH.nameBase n

mkContentFamilyName :: TH.Name -> TH.Name
mkContentFamilyName n = TH.mkName $ TH.nameBase n ++ "Content"

-------------------------------------------------------------------------------
-- emit the code!
-------------------------------------------------------------------------------

defineLanguageFamily :: LanguageFamilyRepr -> [TH.Dec]
defineLanguageFamily LFR
  { lfrTagsAndEntryNTs
  , lfrNonterminals
  , lfrHasFamilies
  , lfrContentFamilies
  }
  =  defineTags lfrTagsAndEntryNTs
  ++ defineNTs lfrNonterminals
  ++ defineHasFams lfrHasFamilies
  ++ defineContentFams lfrContentFamilies

defineTags :: [(LanguageTag, TH.Name)] -> [TH.Dec]
defineTags = map (uncurry defineTag)

defineTag :: LanguageTag -> TH.Name -> TH.Dec
defineTag tag entry =
  TH.NewtypeD noContext
              tag
              noBinders
              noKind
              (TH.NormalC (TH.mkName $ TH.nameBase tag)
                [ asLazyBangType
                $ TH.AppT (TH.ConT entry) (TH.ConT tag) ])
              derivingNothing

defineNTs :: [NonterminalRepr] -> [TH.Dec]
defineNTs = map defineNT

defineNT :: NonterminalRepr -> TH.Dec
defineNT NR{nrName, nrConstrs}
  = TH.DataD noContext
             nrName
             langBndr
             noKind
             (map (defineConstr nrName) nrConstrs)
             derivingNothing

defineConstr :: TH.Name -> ConstrRepr -> TH.Con
defineConstr nrName CR{crName, crHasFamily, crContent} = case crHasFamily of
  Nothing  -> quantPart
  Just hfn -> TH.ForallC langBndr (eqCxt hfn) quantPart
  where
    quantPart = TH.GadtC [crName]
                         (map asLazyBangType $ typesOfConstrContents crContent)
                         (TH.AppT (TH.ConT nrName) (TH.VarT lang))
    eqCxt hfn = [foldl1 TH.AppT [ TH.EqualityT
                                , eqC hfn
                                , TH.PromotedT $ TH.mkName "True"
                                ]]
    eqC hfn = TH.AppT (TH.ConT hfn) (TH.VarT lang)

typesOfConstrContents :: ConstrContents -> [TH.Type]
typesOfConstrContents EmptyConstr = []
typesOfConstrContents (FamilyConstr cfn)
  = [TH.AppT (TH.ConT cfn) (TH.VarT lang)]
typesOfConstrContents (UnchangingConstr ty) = [thIfyContentType ty]

thIfyContentType :: ContentType -> TH.Type
thIfyContentType (SingleContent ty) = ty
thIfyContentType (TupleContent tys) = foldl TH.AppT con tys
  where con = TH.TupleT $ length tys

-- for some reason... BangType is exported from Syntax but not TH?
asLazyBangType :: TH.Type -> TH.BangType
asLazyBangType ty = (TH.Bang TH.NoSourceUnpackedness TH.NoSourceStrictness, ty)

defineHasFams :: [HasFamily] -> [TH.Dec]
defineHasFams = map defineHasFam

defineHasFam :: HasFamily -> TH.Dec
defineHasFam (HasFamily hfn yesTags)
  = TH.ClosedTypeFamilyD famHead $ map mkYesEqn yesTags ++ [elseEq]
  where
    famHead = TH.TypeFamilyHead hfn langBndr (TH.KindSig bool) Nothing
    mkYesEqn tag = TH.TySynEqn [TH.ConT tag] true

    bool   = TH.ConT (TH.mkName "Bool")
    true   = TH.PromotedT (TH.mkName "True")
    false  = TH.PromotedT (TH.mkName "False")
    elseEq = TH.TySynEqn [TH.WildCardT] false

defineContentFams :: [ContentFamily] -> [TH.Dec]
defineContentFams = map defineContentFam

defineContentFam :: ContentFamily -> TH.Dec
defineContentFam (ContentFamily cfn pEqns)
  = TH.ClosedTypeFamilyD famHead $ map mkTySigEqn pEqns
  where
    famHead = TH.TypeFamilyHead cfn langBndr TH.NoSig Nothing
    mkTySigEqn (tag,contentTy)
      = TH.TySynEqn [TH.ConT tag] $ thIfyContentType contentTy

lang :: TH.Name
lang = TH.mkName "lang"

langBndr :: [TH.TyVarBndr]
langBndr = [TH.PlainTV lang]

ntType :: TH.Name -> TH.Type
ntType nt = TH.AppT (TH.ConT nt) (TH.VarT lang)

ntSubType :: TH.Name -> TH.Name -> TH.Type
ntSubType ty lang = TH.AppT (TH.ConT ty) (TH.ConT lang)

listType :: TH.Type -> TH.Type
listType = TH.AppT TH.ListT

unitType :: TH.Type
unitType = TH.TupleT 0

noContext :: TH.Cxt
noContext = []

noBinders :: [TH.TyVarBndr]
noBinders = []

noKind :: Maybe TH.Kind
noKind = Nothing

noConstrs :: [TH.Con]
noConstrs = []

derivingNothing :: [TH.DerivClause]
derivingNothing = []

-------------------------------------------------------------------------------
-- Pipeline
-------------------------------------------------------------------------------

quasiLanguages :: String -> TH.Q [TH.Dec]
quasiLanguages inp = do
  rdr <- parse inp
  let srt = topSortLangFam rdr
  vld <- validateLangFam srt
  rbn <- resolveB vld
  let langs = buildLanguages rbn
  validateMetas langs
  let finLangs = resolveS langs
      fd   = collectFamilyData finLangs
      repr = represent finLangs fd 
  --pPrint repr
  mod <- TH.thisModule
  regDecs <- mapM (Registry.registerLanguage mod) finLangs
  return $ defineLanguageFamily repr ++ regDecs

linguist :: TH.QuasiQuoter
linguist = TH.QuasiQuoter
  { TH.quoteExp  = fail "linguist: top-level splices only"
  , TH.quotePat  = fail "linguist: top-level splices only"
  , TH.quoteType = fail "linguist: top-level splices only"
  , TH.quoteDec  = quasiLanguages
  }

-- Should re-write this one by hand to get the right location
linguistFile :: TH.QuasiQuoter
linguistFile = TH.quoteFile linguist

defineLanguages :: TH.Q [TH.Dec] -> TH.Q [TH.Dec]
defineLanguages = id
