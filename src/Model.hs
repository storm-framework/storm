{-# LANGUAGE GADTs, TypeFamilies, DeriveGeneric, GeneralizedNewtypeDeriving, OverloadedStrings, TemplateHaskell, QuasiQuotes, MultiParamTypeClasses #-}
-- {-# LANGUAGE UndecidableInstances #-}
-- {-@ LIQUID "--no-adt"                   @-}
-- {-@ LIQUID "--exact-data-cons"           @-}
-- {-@ LIQUID "--higherorder"              @-}
-- {-@ LIQUID "--no-termination" @-}
-- | Description of database records.
module Model where

import Data.Functor.Const
import Data.Text (Text)
import Data.Aeson (ToJSON, FromJSON)
import Database.Persist hiding ((==.), (<-.), selectList, selectFirst, insert, entityKey, entityVal) --(PersistField, PersistValue, PersistEntity, Key, EntityField, Unique, Filter, fieldLens, Entity(Entity))
import qualified Database.Persist
import qualified Database.Persist.Sqlite
import qualified Database.Persist.TH
import qualified Data.Text
import qualified Data.Proxy
import qualified GHC.Int
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Data.Functor.Identity (Identity)
import Database.Persist.TH (mkPersist, sqlSettings, persistLowerCase)
import Database.Persist.Sql (SqlBackend, Migration)

import Data.Maybe (fromJust)

import Core

{-@
data EntityFieldWrapper record typ <policy :: Entity record -> Entity User -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool> = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant contravariant invariant invariant @-}


-- ** User
{-@
data User = User
  { userName :: _
  , userSSN :: {v:_ | len v == 9}
  }
@-}

-- TODO: This complains about fromPersistValues, which is legitimate. What should we do?

Database.Persist.TH.share [mkPersist sqlSettings, Database.Persist.TH.mkMigrate "migrateAll"] [persistLowerCase|
User
  name String
  sSN String

TodoItem
  owner UserId
  task String

Share
  from UserId
  to UserId
|]

{-@ userIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> _ _ @-}
userIdField :: EntityFieldWrapper User (Key User)
userIdField = EntityFieldWrapper UserId

{-@ userNameField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userName (entityVal row)}, {\field row -> field == userName (entityVal row)}> _ _ @-}
userNameField :: EntityFieldWrapper User String
userNameField = EntityFieldWrapper UserName

{-@ assume userSSNField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userSSN (entityVal row)}, {\field row -> field == userSSN (entityVal row)}> _ {v:_ | len v == 9} @-}
userSSNField :: EntityFieldWrapper User String
userSSNField = EntityFieldWrapper UserSSN

-- ** TodoItem
{-@
data TodoItem = TodoItem
  { todoItemOwner :: Key User
  , todoItemTask :: {v:_ | len v > 0}
  }
@-}

{-@ todoItemIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> _ _ @-}
todoItemIdField :: EntityFieldWrapper TodoItem (Key TodoItem)
todoItemIdField = EntityFieldWrapper TodoItemId

{-@ todoItemOwnerField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == todoItemOwner (entityVal row)}, {\field row -> field == todoItemOwner (entityVal row)}> _ _ @-}
todoItemOwnerField :: EntityFieldWrapper TodoItem (Key User)
todoItemOwnerField = EntityFieldWrapper TodoItemOwner

{-@ assume todoItemTaskField :: EntityFieldWrapper <{\row viewer -> shared (todoItemOwner (entityVal row)) (entityKey viewer)}, {\row field -> field == todoItemTask (entityVal row)}, {\field row -> field == todoItemTask (entityVal row)}> _ {v:_ | len v > 0} @-}
todoItemTaskField :: EntityFieldWrapper TodoItem String
todoItemTaskField = EntityFieldWrapper TodoItemTask

-- ** Share
{-@
measure shared :: Key User -> Key User -> Bool
@-}

-- {-@
-- data Share where
--   Share :: Key User -> Key User -> {v: Share | shared (shareFrom v) (shareTo v)}
-- @-}

{-@
data Share = Share
  { shareFrom :: Key User
  , shareTo :: Key User
  }
@-}

{-@ invariant {v:Share | shared (shareFrom v) (shareTo v)} @-}


{-@ assume shareIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> _ _ @-}
shareIdField :: EntityFieldWrapper Share (Key Share)
shareIdField = EntityFieldWrapper ShareId

{-@ assume shareFromField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareFrom (entityVal row)}, {\field row -> field == shareFrom (entityVal row)}> _ _ @-}
shareFromField :: EntityFieldWrapper Share (Key User)
shareFromField = EntityFieldWrapper ShareFrom

{-@ assume shareToField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareTo (entityVal row)}, {\field row -> field == shareTo (entityVal row)}> _ _ @-}
shareToField :: EntityFieldWrapper Share (Key User)
shareToField = EntityFieldWrapper ShareTo

