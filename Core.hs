-- | Functionality that needs to be loaded before checking the Models file.

module Binah.Core ( Entity, Key ) where

import Database.Persist (Entity, Key)

-- TODO: This entity stuff is morally just refinements on existing functions
-- from Persist, it would be nice to move this to a spec file.

-- TODO: There's some kind of weird name-resolution problem going on here: I
-- think it would make sense if these measures were named e.g. Core.entityKey,
-- but for some reason that breaks everything, as does auto-generating the
-- measures with e.g. {-@ measure entityKey @-}

{-@ measure entityKey :: Entity record -> Key record @-}

{-@ measure entityVal :: Entity record -> record @-}
