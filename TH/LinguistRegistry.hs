{-# LANGUAGE DeriveGeneric, TupleSections #-}
module TH.LinguistRegistry where

import TH.LanguageFamilyRepr

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

import qualified Data.HashMap.Strict as H
import Data.Hashable (Hashable(..))

import Control.Monad (when, mplus)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT, runMaybeT))

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import System.Directory (getAppUserDataDirectory, createDirectoryIfMissing)
import System.FilePath

import GHC.Generics (Generic)

-------------------------------------------------------------------------------
-- Known languages
-------------------------------------------------------------------------------

data RenamedLanguageTag
  = RLT !TH.Module !TH.OccName
  deriving (Eq, Show, Generic)

instance Hashable TH.Module
instance Hashable TH.PkgName
instance Hashable TH.ModName
instance Hashable TH.OccName
instance Hashable RenamedLanguageTag

fromModule :: TH.Module -> RenamedLanguageTag -> Bool
fromModule n (RLT n' _) = n == n'

nameModule :: TH.Name -> Maybe TH.Module
nameModule n = do
  pkg <- TH.namePackage n
  mod <- TH.nameModule  n
  return $ TH.Module (TH.PkgName pkg) (TH.ModName mod)

nameOccName :: TH.Name -> TH.OccName
nameOccName (TH.Name occ _) = occ

rltThName :: RenamedLanguageTag -> TH.Name
rltThName (RLT (TH.Module (TH.PkgName pkg) (TH.ModName mod)) occ)
  = TH.mkNameG_tc pkg mod $ TH.occString occ

type LanguageRep = Fin Language
type Registry = H.HashMap RenamedLanguageTag LanguageRep

-- | The registry of language families defined during this compilation.
-- Languages not in the registry can be looked up from their annotation,
-- if it exists, otherwise we don't know about it :(
--
-- Languages looked up via annotation will appear here too.
registry :: IORef Registry
registry = unsafePerformIO (newIORef H.empty)
{-# NOINLINE registry #-}

{- [Note: external storage location]
Initially, we tried to externally store representations in files.
This worked, but TH supports GHC annotations so we can do that instead!
-}

-- | Register the given language in the compilation-local registry and
-- also return a declaration that will register the language for universal
-- lookup.
registerLanguage :: TH.Module -> Fin Language -> TH.Q TH.Dec
registerLanguage mod fl = do
  let rlt = RLT mod $ nameOccName $ langName fl
  registerIfNotInteractive rlt fl
  liftedFL <- TH.lift fl
  return $ TH.PragmaD $ TH.AnnP (TH.TypeAnnotation (langName fl)) liftedFL

lookupRenamedLanguageTag :: TH.Name -> TH.Q (Maybe RenamedLanguageTag)
lookupRenamedLanguageTag n = do
  let base = TH.nameBase n
  mname <- TH.lookupTypeName base
  let mNameMod = do name <- mname; (name,) <$> nameModule name
  return $! case mNameMod of
    Nothing -> Nothing
    Just (TH.Name occ _flav, mod) -> Just $ RLT mod occ

lookupLanguage :: TH.Name -> TH.Q (Maybe LanguageRep)
lookupLanguage name = do
  mrlt <- lookupRenamedLanguageTag name
  case mrlt of
    Nothing -> do
      TH.reportError $ makeRltErr name
      return Nothing
    Just rlt -> do
      mlfr <- runMaybeT $
        MaybeT ((H.!? rlt) <$> TH.runIO (readIORef registry))
          `mplus` MaybeT (findAnnotated rlt)
      case mlfr of
        Nothing -> do
          TH.reportError $ makeLookupErr name
          return Nothing
        Just lfr -> return $ Just lfr

findAnnotated :: RenamedLanguageTag -> TH.Q (Maybe LanguageRep)
findAnnotated rlt = do
  anns <- TH.reifyAnnotations (TH.AnnLookupName n) :: TH.Q [LanguageRep]
  case anns of
    [rep] -> do
      registerIfNotInteractive rlt rep
      return $ Just rep
    [] -> do TH.reportError $ makeLookupErr n; pure Nothing
    _ -> do fail $ makeMultipleRepErr n
  where
    n = rltThName rlt

registerIfNotInteractive :: RenamedLanguageTag -> LanguageRep -> TH.Q ()
registerIfNotInteractive rlt@(RLT (TH.Module (TH.PkgName pkg) _) _) rep
  | pkg `elem` ["main", "interactive"] = pure ()
  | otherwise = TH.runIO $ modifyIORef' registry (H.insert rlt rep)

makeRltErr :: TH.Name -> String
makeRltErr name = unlines
  [ "Can't find type name `" ++ show name ++ "'."
  , "Perhaps you need to import it?"
  ]

makeLookupErr :: TH.Name -> String
makeLookupErr name = unlines
  [ "Unknown language `" ++ show name ++ "'."
  , "I was able to find the type name, but not the language representation."
  , "If the language is not in this package, ensure that the same version of Linguist was used"
  , "to compile both the language definition and this package."
  , "Otherwise, report a bug!"
  ]

makeMultipleRepErr :: TH.Name -> String
makeMultipleRepErr name = unlines
  [ "Found multiple representations for language `" ++ show name ++ "'."
  , "I'm not sure how this happened (I thought it wasn't possible!)"
  , "If the language is not in this package, ensure that the same version of Linguist was used"
  , "to compile both the language definition and this package."
  , "Otherwise, report a bug!"
  ]
