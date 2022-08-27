module Passes.LispIL.CopyCoalesce
  ( copyCoalesce ) where

import Control.Monad.State.Strict
import Data.Functor (($>), (<&>))
import Data.IntMap.Strict
import Data.Maybe (fromMaybe)

import Language.LispIL.CPS

copyCoalesce :: Syntax -> Syntax
-- Note the top-down traversal. We have to make sure that we've seen
-- each potential binding copy _before_ we try to replace the uses!
copyCoalesce = flip evalState empty . traverseCpsTD go

type VarMap = IntMap Binding
-- personal note: for performance reasons we actually want to be able to
-- execute "before" operations (bottom-up) and "after" operations (top-down)
-- on each node. For example, here I'd like to remove a key from the map once
-- we finish transforming the node that was the binding site.
-- It's not important, because the bound names are globally unique, but it
-- is the best practice.
type Coalesce = State VarMap

-- | 'markCopy' x y indicates that binding x is defined as a copy of binding y.
-- If binding y is already marked as a binding of something else, that is
-- propogated to x (so it is safe to delete the binding of x entirely).
--
-- Note that this is only safe because LispIL does not support local mutable variables.
markCopy :: Binding -> Binding -> Coalesce ()
markCopy (External _n) _ = pure ()
markCopy (Internal _n i) copied = do
  trueBinding <- replace copied <&> fromMaybe copied
  modify $ insert i trueBinding

replace :: Binding -> Coalesce (Maybe Binding)
replace (External _n) = pure Nothing
replace (Internal _n i) = gets (!? i)

go :: Syntax -> Coalesce (Maybe Syntax)
go (Ref b) = fmap Ref <$> replace b
go (Let (x, Ref y) b) = markCopy x y $> Just b
go _ = pure Nothing
