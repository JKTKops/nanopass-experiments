{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.LispIL.Binding where

import Control.Monad.State.Strict

data Binding = External String
             | Internal String Int

bindingNum :: Binding -> Maybe Int
bindingNum External{} = Nothing
bindingNum (Internal _ n) = Just n

instance Eq Binding where
  External a == External b = a == b
  Internal _ u == Internal _ v = u == v
  _ == _ = False

instance Ord Binding where
  External{} `compare` Internal{} = LT
  Internal{} `compare` External{}  = GT
  External a `compare` External b = a `compare` b
  Internal _ u `compare` Internal _ v = u `compare` v

instance Show Binding where
  showsPrec _ (External n) = showString n
  showsPrec _ (Internal n i) = showString n . showChar '.' . shows i

newtype Fresh a = Fresh (State Int a)
  deriving (Functor, Applicative, Monad)

fresh :: String -> Fresh Binding
fresh n = Fresh $ state $ \i -> (Internal n i, i+1)

runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

runFreshFrom :: Int -> Fresh a -> (a, Int)
runFreshFrom i (Fresh m) = runState m i
