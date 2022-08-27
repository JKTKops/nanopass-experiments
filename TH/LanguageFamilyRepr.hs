{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving, DeriveDataTypeable, DeriveLift #-}
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}
module TH.LanguageFamilyRepr where

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.PprLib hiding ((<>))
import qualified Language.Haskell.TH.PprLib as Ppr

import Data.Data (Data)
import Data.Hashable (Hashable(..))
import qualified Data.HashMap.Strict as H

-------------------------------------------------------------------------------
-- TH orphan lift instances
-- who knows why these aren't in the th package
-------------------------------------------------------------------------------

deriving instance Lift TH.Name
deriving instance Lift TH.NameFlavour
deriving instance Lift TH.ModName
deriving instance Lift TH.PkgName
deriving instance Lift TH.NameSpace
deriving instance Lift TH.OccName

deriving instance Lift TH.Type
deriving instance Lift TH.TyVarBndr
deriving instance Lift TH.TyLit

instance (Lift k, Lift v) => Lift (H.HashMap k v) where
  -- This strange method of definition is because sometimes GHC decides it
  -- it wants to apply lift to the thing inside the splice... but that leads
  -- to a recursive lift @HashMap. Doing it this way ensures that that would
  -- be a type error, but it also seems to prevent GHC from trying to do
  -- that at all. Yay.
  lift m = [e| H.fromList $(listM) |]
    where listM = lift $ H.toList m

---------------------------------------

type LanguageTag = TH.Name
instance Hashable TH.Name where
  hashWithSalt s n = hashWithSalt s (show n)

type HasFamilyName = TH.Name
data HasFamily = HasFamily HasFamilyName [LanguageTag]
  deriving (Show)

data ContentType = SingleContent TH.Type | TupleContent [TH.Type]
  deriving (Eq, Show)
type ContentFamilyName = TH.Name
data ContentFamily
  = ContentFamily ContentFamilyName [(LanguageTag, ContentType)]
  deriving (Show)

data NonterminalRepr = NR
  { nrName :: TH.Name
  , nrConstrs :: [ConstrRepr]
  }
  deriving (Show)

data ConstrContents
  = EmptyConstr
  | FamilyConstr ContentFamilyName
  | UnchangingConstr ContentType
  deriving (Show)

data ConstrRepr = CR
  { crName      :: TH.Name
  , crHasFamily :: Maybe HasFamilyName
  , crContent   :: ConstrContents
  }
  deriving (Show)

data LanguageFamilyRepr = LFR
  { lfrTagsAndEntryNTs :: [(LanguageTag, TH.Name)]
  , lfrNonterminals    :: [NonterminalRepr]
  , lfrHasFamilies     :: [HasFamily]
  , lfrContentFamilies :: [ContentFamily]
  }
  deriving (Show)

viewTH :: TH.Ppr a => TH.Q a -> IO ()
viewTH q = TH.runQ q >>= putStrLn . TH.pprint

-------------------------------------------------------------------------------
-- Support Data Types
--
-- A new group of language definitions will insert a bunch of Language
-- structures into the global hashmap of languages we know about, I think.
-------------------------------------------------------------------------------

newtype BigName = BigName String
  deriving (Eq, Ord, Hashable)
newtype SmallName = SmallName String
  deriving (Eq, Hashable, Data, Lift)
newtype MetaName = MetaName SmallName
  deriving (Eq, Hashable, Data, Lift)
instance Show BigName where
  show (BigName n) = n
instance Show SmallName where
  show (SmallName n) = n
instance Show MetaName where
  show (MetaName n) = show n

type Fin f = f TH.Name (MetaName,TH.Type)

newtype NtTag nameTy _eltTy = NtTag {getNtTag :: nameTy}
  deriving (Data, Lift)

instance Show n => Show (NtTag n e) where
  show (NtTag n) = show n

-- these are parameterized because originally I was planning on using
-- bifunctor instances to do get string->Name transformations...
-- but it ended up not working out that way so use Rdr Thing.

data Language nameTy eltTy = Language
  { langName          :: nameTy
  , langEntry         :: nameTy
    -- map meta-names to the correct language objects
  -- metaname |-> Terminal
  , langTerminals     :: MetaCollection Terminal nameTy eltTy
  -- metaname |-> Nonterminal name
  , langNonterminalMC :: MetaCollection NtTag nameTy eltTy
  -- Nonterminal name |-> nonterminal entity
  , langNonterminals  :: H.HashMap nameTy (Nonterminal nameTy eltTy)
  -- , langDelta         :: Maybe (LanguageDelta nameTy eltTy)
  }

deriving instance Data (Fin Language)
deriving instance Lift (Fin Language)

deriving instance
  ( Show nameTy
  , Show eltTy
  , Show (Metanames eltTy)
  , Show (MetaCollection Terminal nameTy eltTy)
  , Show (MetaCollection NtTag nameTy eltTy)
  ) => Show (Language nameTy eltTy)

type family MetaCollection b nameTy eltTy where
  MetaCollection b nameTy SmallName = [(SmallName, b nameTy SmallName)]
  MetaCollection b nameTy MetaName  = H.HashMap MetaName (b nameTy MetaName)
  MetaCollection b nameTy eltTy = [b nameTy eltTy]

data Terminal nameTy eltTy = Terminal
  { terminalTypeName :: nameTy
  , terminalMetanames :: Metanames eltTy
  }

deriving instance Data (Fin Terminal)
deriving instance Lift (Fin Terminal)
deriving instance (Show nameTy, Show (Metanames eltTy)) => Show (Terminal nameTy eltTy)

type family Metanames eltTy where
  Metanames SmallName = [SmallName]
  Metanames _  = [MetaName]

data Nonterminal nameTy eltTy = Nonterminal
  { nonterminalName      :: nameTy
  , nonterminalConstrs   :: H.HashMap nameTy (LangConstr nameTy eltTy)
  , nonterminalMetanames :: Metanames eltTy
  }

deriving instance (Show nameTy, Show eltTy, Show (Metanames eltTy))
  => Show (Nonterminal nameTy eltTy)
deriving instance Data (Fin Nonterminal)
deriving instance Lift (Fin Nonterminal)

data LangConstr nameTy eltTy = LangConstr
  { constrName     :: nameTy
  , constrSrcNt    :: nameTy
  , constrContents :: [ConstrElt nameTy eltTy]
  }
  deriving (Show)

deriving instance Data (Fin LangConstr)
deriving instance Lift (Fin LangConstr)

data ConstrElt nameTy eltTy
  = PureElt eltTy
  | ListElt [ConstrElt nameTy eltTy]
  | AppElt nameTy (ConstrElt nameTy eltTy) -- e.g. Maybe e; the name must be in scope

deriving instance Data (Fin ConstrElt)
deriving instance Lift (Fin ConstrElt)

instance (Show nameTy, Show eltTy) => Show (ConstrElt nameTy eltTy) where
  showsPrec n (PureElt e) = showsPrec n e
  showsPrec _ (ListElt []) = error "ConstrElt: empty ListElt"
  showsPrec _ (ListElt [e]) = showChar '[' . shows e . showChar ']'
  showsPrec _ (ListElt es) = showString "[(" . foldr1 ((.) . (. showChar ',')) (map shows es) . showString ")]"
  showsPrec n (AppElt ty e) = showParen (n >= 11) $ shows ty . showChar ' ' . showsPrec 11 e

data LanguageDelta nameTy eltTy = LanguageDelta
  { extensionName    :: nameTy
  , sourceLanguage   :: nameTy
  , newLangEntry     :: Maybe nameTy
  , terminalDelta    :: TerminalDelta nameTy eltTy
  , nonterminalDelta :: NonterminalDelta nameTy eltTy
  }

deriving instance
  ( Show nameTy
  , Show eltTy
  , Show (Metanames eltTy)
  , Show (MetaCollection Terminal nameTy eltTy)
  , Show (MetaCollection NtTag nameTy eltTy)
  ) => Show (LanguageDelta nameTy eltTy)

-- These ones use 'eltTy' as the hashmap entry because 
data TerminalDelta nameTy eltTy = TerminalDelta
  { removedTerminals :: [eltTy]
  , addedTerminals   :: MetaCollection Terminal nameTy eltTy
  }

deriving instance (Show eltTy, Show (MetaCollection Terminal nameTy eltTy))
  => Show (TerminalDelta nameTy eltTy)

data NonterminalDelta nameTy eltTy = NonterminalDelta
  { removedNonterminals  :: [nameTy]
  , addedNonterminalsMC  :: MetaCollection NtTag nameTy eltTy
  , addedNonterminals    :: H.HashMap nameTy (Nonterminal nameTy eltTy)
  , modifiedNonterminals :: H.HashMap nameTy (OneNonterminalDelta nameTy eltTy)
  }

deriving instance
  ( Show nameTy
  , Show eltTy
  , Show (Metanames eltTy)
  , Show (MetaCollection NtTag nameTy eltTy)
  ) => Show (NonterminalDelta nameTy eltTy)

data OneNonterminalDelta nameTy eltTy = OneNonterminalDelta
  { removedConstrs :: [nameTy]
  , addedConstrs   :: H.HashMap nameTy (LangConstr nameTy eltTy)
  }
  deriving Show

-------------------------------------------------------------------------------
-- Pretty instances
-------------------------------------------------------------------------------

instance Ppr MetaName where
  ppr = text . show

instance Ppr (Fin Terminal) where
  ppr (Terminal ty mns)
    = hsep (punctuate comma (map ppr mns)) <+> dcolon <+> text (nameBase ty)

instance Ppr (Fin ConstrElt) where
  ppr = pprConstrElt True

pprConstrElt :: Bool -> Fin ConstrElt -> Doc
pprConstrElt parenCxt = \case
  PureElt (mn,_ty) -> ppr mn
  ListElt es -> brackets $ ps $ hsep $ punctuate comma $ map (pprConstrElt False) es
    where ps = if not (null $ tail es) then parens else id
  AppElt w e ->
    let wrap = if parenCxt then parens else id
    in wrap $ text (nameBase w) <+> pprConstrElt True e

instance Ppr (Fin LangConstr) where
  ppr LangConstr{constrName,constrContents}
    = text (nameBase constrName) <+> hsep (map ppr constrContents)

vbar :: Doc
vbar = char '|'

instance Ppr (Fin Nonterminal) where
  ppr Nonterminal{nonterminalName, nonterminalConstrs, nonterminalMetanames}
    = hsep (punctuate comma (map ppr mns)) <+> dcolon <+> text (nameBase nonterminalName)
    $$ nest 2 (formatCs $ H.elems nonterminalConstrs)
    where
      formatCs [] = empty
      formatCs (c:cs) = equals <+> ppr c $$ vcat (map ((vbar <+>) . ppr) cs) $$ semi
      mns = nonterminalMetanames

instance Ppr (Fin Language) where
  ppr Language{langName, langEntry, langTerminals, langNonterminals}
    = text "language" <+> text (nameBase langName) <+> text "where"
    $$ nest 2 (text "entry" <+> text (nameBase langEntry))
    $$ nest 2 (text "terminals")
    $$ nest 4 (vcat (map ppr langTerminals) <> semi)
    $+$ space
    $+$ nest 2 (nts $ H.elems langNonterminals)
    where
      nts [] = empty
      nts ns = foldr1 ($=$) (map ppr ns)

($=$) :: Doc -> Doc -> Doc
a $=$ b = a $+$ space $+$ b

instance Semigroup Doc where
  (<>) = (Ppr.<>)

instance Monoid Doc where
  mempty  = empty
  mappend = (<>)
