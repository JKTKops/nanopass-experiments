{-# LANGUAGE TypeFamilies #-}
module Passes.LispIL.ExpandApply
  ( expandApply )
  where


import           Language.LispIL.Syntax hiding (Syntax)
import qualified Language.LispIL.Syntax as Apply
import           Language.LispIL.ExpandApply hiding (Syntax)
import qualified Language.LispIL.ExpandApply as NoApply

-- Separation of concerns!
-- We can assume that 'apply' has only been inserted in the places it belongs,
-- and expand it everywhere uniformly.
--
-- We use the good expansion from the paper. There's not really a point in
-- in even supporting the Duplicate strategy. It's awful.
-- However at this point we're also beginning to deal with with the
-- introduction of new variables, so now we need a fresh variable monad.
--
-- I think if we were truly separating concerns, we would insert non-uniqued
-- variables here and let a different pass rename them. But also like...
-- that seems like separating things a bit _too_ much, lol.
expandApply :: Apply.Syntax -> Fresh NoApply.Syntax
expandApply (Ref "apply") = error "Passes.LispIL.ExpandApply: unsaturated apply form"
expandApply (Ref n) = pure $ Ref (External n)
expandApply (Set n e) = Set (External n) <$> expandApply e
expandApply (Seq es) = Seq <$> traverse expandApply es
expandApply (Cnd b t f)
  = Cnd <$> expandApply b <*> expandApply t <*> expandApply f
expandApply (App (App (Ref "apply") f) g) = do
  evalF  <- fresh "f"
  delayG <- fresh "gp"
  f'     <- expandApply f
  g'     <- expandApply g
  return $
    Let [(evalF, f'), (delayG, Abs g')] $
      Cnd (PtrEq (Ref (External "d")) (Ref evalF))
          (Ref delayG) $
            App (Term (Ref evalF)) (App Force (Ref delayG))
expandApply (App f g) = reconstruct <$> expandApply f <*> expandApply g
  where reconstruct fe ge = App (Term fe) ge
-- More boilerplate in language separation could get rid of the cases that
-- this covers (halt and ptreq).
expandApply _ = error "Passes.LispIL.ExpandApply: illegal term."
