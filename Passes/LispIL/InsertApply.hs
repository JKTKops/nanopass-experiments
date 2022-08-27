module Passes.LispIL.InsertApply where

import Language.LispIL.Syntax

-- Insert 'apply' forms in wherever we can't prove that they
-- aren't necessary. For now, we aren't trying to do a good
-- job, because we're more interested in experimenting with
-- this Trees-That-Change approach to nanopass design.
--
-- This has to happen before applyExpansion, which has to
-- happen before CPS because it introduces abstractions.
--
-- In a true nanopass framework where creating new variations
-- is cheap, this would be a transformation from Syntax'Base 
-- to Syntax'ExplicitApply or something like that.
-- That boilerplate would also let the App form's contents more
-- accurately reflect the changing structure.
-- But writing boilerplate kinda sucks (that's the point!)
-- So I'm only focusing on the major steps here.
insertApply :: Syntax -> Syntax
insertApply s@(App (Ref "apply") _) = s
insertApply (App h e) = App (App (Ref "apply") (insertApply h)) (insertApply e)
insertApply (Seq es) = Seq $ map insertApply es
insertApply (Ref n) = Ref n
insertApply (Set n e) = Set n $ insertApply e
insertApply (Cnd b t f) = Cnd (insertApply b) (insertApply t) (insertApply f)

{-
insertApply Halt{} = error ":("
insertApply PtrEq{} = error ":("
-}
insertApply _ = error ":("