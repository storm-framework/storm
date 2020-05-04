-- | Where we define the model. Pretty much every module has to load this,
-- because various definitions need to know about User -- it would be nice to
-- decouple these.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Model where

import Database.Persist (Key)
import qualified Database.Persist as Persist
import Database.Persist.TH (share, mkMigrate, mkPersist, sqlSettings, persistLowerCase)
import Data.Text (Text)
import qualified Data.Text as Text

import Binah.Core

-- We need this wrapper because Liquid Haskell just has no idea what to do with
-- GADT data families like EntityField. Hiding it inside a plain data type makes
-- checking much more stable. Eventually it would be nice to be able to remove
-- this wrapper.
--
-- The `policy` absref specifies who can view a given record. The `selector` and
-- `flippedselector` connects the EntityFieldWrapper to the field selector it
-- represents. These absrefs should be the same, just with their arguments
-- flipped.


-- * Model

-- Generate the Persistent data types for the model. We refine some of those
-- data types below. Ideally these two steps would be integrated somehow.
--
-- TODO: We should restrict access to some of the functions in this type class
-- like fieldLens and fromPersistValues.
--
-- TODO: It would be nice if we could check this file without getting errors
-- about e.g. methods which take Void throwing errors. We need to be able to
-- {-@ ignore _ @-} instance methods to do this, I think.

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  name Text
  ssn Text !policy="entityKey viewer == entityKey row"

TodoItem
  owner UserId
  task Text !policy="shared (todoItemOwner (entityVal row)) (entityKey viewer)"

Share !invariant={v:Share | shared (shareFrom v) (shareTo v)}
  from UserId
  to UserId
|]

-- * User
{-@
data User = User
  { userName :: _
  , userSsn :: {v:_ | tlen v == 9}
  }
@-}

{-@ assume userIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> (Entity User) User UserId @-}
userIdField :: EntityFieldWrapper (Entity User) User UserId
userIdField = EntityFieldWrapper UserId

{-@ assume userNameField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userName (entityVal row)}, {\field row -> field == userName (entityVal row)}> (Entity User) _ _ @-}
userNameField :: EntityFieldWrapper (Entity User) User Text
userNameField = EntityFieldWrapper UserName

{-@ assume userSsnField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userSsn (entityVal row)}, {\field row -> field == userSsn (entityVal row)}> (Entity User) _ {v:_ | tlen v == 9} @-}
userSsnField :: EntityFieldWrapper (Entity User) User Text
userSsnField = EntityFieldWrapper UserSsn

-- * TodoItem
{-@
data TodoItem = TodoItem
  { todoItemOwner :: Key User
  , todoItemTask :: {v:_ | tlen v > 0}
  }
@-}

{-@ assume todoItemIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> (Entity User) _ _ @-}
todoItemIdField :: EntityFieldWrapper (Entity User) TodoItem (Key TodoItem)
todoItemIdField = EntityFieldWrapper TodoItemId

{-@ assume todoItemOwnerField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == todoItemOwner (entityVal row)}, {\field row -> field == todoItemOwner (entityVal row)}> (Entity User) _ _ @-}
todoItemOwnerField :: EntityFieldWrapper (Entity User) TodoItem (Key User)
todoItemOwnerField = EntityFieldWrapper TodoItemOwner

{-@ assume todoItemTaskField :: EntityFieldWrapper <{\row viewer -> shared (todoItemOwner (entityVal row)) (entityKey viewer)}, {\row field -> field == todoItemTask (entityVal row)}, {\field row -> field == todoItemTask (entityVal row)}> (Entity User) _ {v:_ | tlen v > 0} @-}
todoItemTaskField :: EntityFieldWrapper (Entity User) TodoItem Text
todoItemTaskField = EntityFieldWrapper TodoItemTask

-- * Share
{-@
data Share = Share
  { shareFrom :: Key User
  , shareTo :: Key User
  }
@-}

-- This measure represents the abstract relationship that the first user has
-- shared something with the second user. It's attached to the database record
-- that attests that relationship.
--
-- TODO: It's at least inadivsable, and possibly unsound, to assume that this
-- relationship holds for any `Shared`. Really what we want is to know that it
-- holds for any `Shared` that we get back from the database. It's not clear how
-- to do this parametrically, though.
{-@ measure shared :: Key User -> Key User -> Bool @-}
{-@ invariant {v:Share | shared (shareFrom v) (shareTo v)} @-}

{-@ assume shareIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> (Entity User) _ _ @-}
shareIdField :: EntityFieldWrapper (Entity User) Share (Key Share)
shareIdField = EntityFieldWrapper ShareId

{-@ assume shareFromField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareFrom (entityVal row)}, {\field row -> field == shareFrom (entityVal row)}> (Entity User) _ _ @-}
shareFromField :: EntityFieldWrapper (Entity User) Share (Key User)
shareFromField = EntityFieldWrapper ShareFrom

{-@ assume shareToField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareTo (entityVal row)}, {\field row -> field == shareTo (entityVal row)}> (Entity User) _ _ @-}
shareToField :: EntityFieldWrapper (Entity User) Share (Key User)
shareToField = EntityFieldWrapper ShareTo
