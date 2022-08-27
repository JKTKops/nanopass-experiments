module TH.DisplayLanguage where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import TH.LanguageFamilyRepr
import TH.LinguistRegistry

-- | Given the name of a language, create an expression string representing
-- Linguist source that would define that language from scratch
-- (i.e., not as an extension).
showLanguageQ :: Name -> Q String
showLanguageQ n = do
  mrepr <- lookupLanguage n
  case mrepr of
    Nothing -> fail "Can't display language without representation."
    Just repr -> return $ pprint repr

quoteShowLanguage :: Name -> Q Exp
quoteShowLanguage n = showLanguageQ n >>= lift

-- | Splicing @$(displayLanguage ''LanguageName)@ will print the representation
-- of the language, making it appear as a base language even if it was defined
-- as an extension. The spliced expression is just ().
--
-- Intended for use in the REPL.
displayLanguage :: Name -> Q Exp
displayLanguage n = showLanguageQ n >>= runIO . putStrLn >> return (TupE [])
