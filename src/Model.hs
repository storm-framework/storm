{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--compile-spec" @-}

module Model 
  ( EntityFieldWrapper(..)
  , migrateAll
  , BinahRecord
  , persistentRecord
  , mkUser
  , mkTodoItem
  , mkShare
  , User
  , TodoItem
  , Share
  , userId'
  , userName'
  , userSsn'
  , todoItemId'
  , todoItemOwner'
  , todoItemTask'
  , shareId'
  , shareFrom'
  , shareTo'
  , UserId
  , TodoItemId
  , ShareId
  )

where

import           Database.Persist               ( Key )
import           Database.Persist.TH            ( share
                                                , mkMigrate
                                                , mkPersist
                                                , sqlSettings
                                                , persistLowerCase
                                                )
import           Data.Text                      ( Text )
import qualified Database.Persist              as Persist

import           Binah.Core

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
  name Text
  ssn Text

TodoItem
  owner UserId
  task Text

Share
  from UserId
  to UserId
|]

{-@
data EntityFieldWrapper record typ < querypolicy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   , capability :: Entity record -> Bool
                                   , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                                   > = EntityFieldWrapper _
@-}

data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant invariant invariant @-}

{-@ measure currentUser :: Entity User @-}

--------------------------------------------------------------------------------
-- | Predicates
--------------------------------------------------------------------------------

{-@ measure shared :: UserId -> UserId -> Bool @-}

--------------------------------------------------------------------------------
-- | Policies
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- | Records
--------------------------------------------------------------------------------

{-@ data BinahRecord record < 
    p :: Entity record -> Bool
  , insertpolicy :: Entity record -> Entity User -> Bool
  , querypolicy  :: Entity record -> Entity User -> Bool 
  >
  = BinahRecord _
@-}
data BinahRecord record = BinahRecord record
{-@ data variance BinahRecord invariant invariant invariant invariant @-}

{-@ persistentRecord :: BinahRecord record -> record @-}
persistentRecord :: BinahRecord record -> record
persistentRecord (BinahRecord record) = record

{-@ measure getJust :: Key record -> Entity record @-}

-- * User
{-@ mkUser :: 
     x_0: Text
  -> x_1: Text
  -> BinahRecord < 
       {\row -> userName (entityVal row) == x_0 && userSsn (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\x_0 x_1 -> (entityKey x_1 == entityKey x_0)}
     > User
@-}
mkUser x_0 x_1 = BinahRecord (User x_0 x_1)

{-@ invariant {v: Entity User | v == getJust (entityKey v)} @-}



{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ measure userName :: User -> Text @-}

{-@ measure userNameCap :: Entity User -> Bool @-}

{-@ assume userName' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  , {\old -> userNameCap old}
  , {\old _ _ -> userNameCap old}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ measure userSsn :: User -> Text @-}

{-@ measure userSsnCap :: Entity User -> Bool @-}

{-@ assume userSsn' :: EntityFieldWrapper <
    {\x_0 x_1 -> (entityKey x_1 == entityKey x_0)}
  , {\row field  -> field == userSsn (entityVal row)}
  , {\field row  -> field == userSsn (entityVal row)}
  , {\old -> userSsnCap old}
  , {\old _ _ -> userSsnCap old}
  > _ _
@-}
userSsn' :: EntityFieldWrapper User Text
userSsn' = EntityFieldWrapper UserSsn

-- * TodoItem
{-@ mkTodoItem :: 
     x_0: UserId
  -> x_1: Text
  -> BinahRecord < 
       {\row -> todoItemOwner (entityVal row) == x_0 && todoItemTask (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\x_0 x_1 -> (shared (todoItemOwner (entityVal x_0)) (entityKey x_1))}
     > TodoItem
@-}
mkTodoItem x_0 x_1 = BinahRecord (TodoItem x_0 x_1)

{-@ invariant {v: Entity TodoItem | v == getJust (entityKey v)} @-}



{-@ assume todoItemId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
todoItemId' :: EntityFieldWrapper TodoItem TodoItemId
todoItemId' = EntityFieldWrapper TodoItemId

{-@ measure todoItemOwner :: TodoItem -> UserId @-}

{-@ measure todoItemOwnerCap :: Entity TodoItem -> Bool @-}

{-@ assume todoItemOwner' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == todoItemOwner (entityVal row)}
  , {\field row  -> field == todoItemOwner (entityVal row)}
  , {\old -> todoItemOwnerCap old}
  , {\old _ _ -> todoItemOwnerCap old}
  > _ _
@-}
todoItemOwner' :: EntityFieldWrapper TodoItem UserId
todoItemOwner' = EntityFieldWrapper TodoItemOwner

{-@ measure todoItemTask :: TodoItem -> Text @-}

{-@ measure todoItemTaskCap :: Entity TodoItem -> Bool @-}

{-@ assume todoItemTask' :: EntityFieldWrapper <
    {\x_0 x_1 -> (shared (todoItemOwner (entityVal x_0)) (entityKey x_1))}
  , {\row field  -> field == todoItemTask (entityVal row)}
  , {\field row  -> field == todoItemTask (entityVal row)}
  , {\old -> todoItemTaskCap old}
  , {\old _ _ -> todoItemTaskCap old}
  > _ _
@-}
todoItemTask' :: EntityFieldWrapper TodoItem Text
todoItemTask' = EntityFieldWrapper TodoItemTask

-- * Share
{-@ mkShare :: 
     x_0: UserId
  -> x_1: UserId
  -> BinahRecord < 
       {\row -> shareFrom (entityVal row) == x_0 && shareTo (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\x_0 x_1 -> False}
     > Share
@-}
mkShare x_0 x_1 = BinahRecord (Share x_0 x_1)

{-@ invariant {v: Entity Share | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity Share | shared (shareFrom (entityVal v)) (shareTo (entityVal v))} @-}

{-@ assume shareId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  , {\_ -> False}
  , {\_ _ _ -> True}
  > _ _
@-}
shareId' :: EntityFieldWrapper Share ShareId
shareId' = EntityFieldWrapper ShareId

{-@ measure shareFrom :: Share -> UserId @-}

{-@ measure shareFromCap :: Entity Share -> Bool @-}

{-@ assume shareFrom' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == shareFrom (entityVal row)}
  , {\field row  -> field == shareFrom (entityVal row)}
  , {\old -> shareFromCap old}
  , {\old _ _ -> shareFromCap old}
  > _ _
@-}
shareFrom' :: EntityFieldWrapper Share UserId
shareFrom' = EntityFieldWrapper ShareFrom

{-@ measure shareTo :: Share -> UserId @-}

{-@ measure shareToCap :: Entity Share -> Bool @-}

{-@ assume shareTo' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == shareTo (entityVal row)}
  , {\field row  -> field == shareTo (entityVal row)}
  , {\old -> shareToCap old}
  , {\old _ _ -> shareToCap old}
  > _ _
@-}
shareTo' :: EntityFieldWrapper Share UserId
shareTo' = EntityFieldWrapper ShareTo

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------


