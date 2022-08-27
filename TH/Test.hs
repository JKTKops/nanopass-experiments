{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, ViewPatterns #-}
module TH.Test where

import qualified Data.Set as S
import TH.DefineLanguage
import TH.QuoteLanguage
import TH.DefinePass

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH

data Binding = Internal String | External String Int deriving (Eq, Show)
type CodePointer = Int
type FreeVars = S.Set Binding

pure [] -- create a declaration group so Linguist can see the types above
[linguistFile|TH/example.lng|]
pure []

fromMaybe :: a -> Maybe a -> a
fromMaybe def Nothing = def
fromMaybe _ (Just x) = x

definePass [d|
  twoArmIf :: Simple -> TwoArmIf
  twoArmIf (Simple ir) = TwoArmIf (stmt ir)

  stmt :: Transform' Statement Statement
  stmt (If e (R (stmt -> s1)) Nothing) = If e s1 $ Exp 0
  stmt (If e (R (stmt -> s1)) (Just (R (stmt -> s2)))) = If e s1 s2
  stmt (If e (R (stmt -> s1)) (R (fmap stmt -> ms2))) = If e s1 (fromMaybe (Exp 0) ms2)
  stmt (Exp i) = Exp i
  stmt (While i (R (stmt -> s))) = While i s
  stmt (Block (R (map stmt -> ss))) = Block ss
 |]

definePass [d|
  noWhile :: TwoArmIf -> NoWhile
  noWhile (TwoArmIf ir) = NoWhile (stmt ir)

  stmt :: Transform' Statement Statement
  stmt (While i (R (stmt -> b))) = Block [Label "L", If True (Block [b, Goto "L"]) (Exp False)]
 |]
