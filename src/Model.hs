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
data EntityFieldWrapper record typ < policy :: Entity record -> Entity User -> Bool
                                   , selector :: Entity record -> typ -> Bool
                                   , flippedselector :: typ -> Entity record -> Bool
                                   > = EntityFieldWrapper _
@-}

data EntityFieldWrapper record typ = EntityFieldWrapper (Persist.EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant invariant invariant invariant @-}

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

{-@ measure userName :: User -> Text @-}
{-@ measure userSsn :: User -> Text @-}

{-@ mkUser :: 
     x_0: Text
  -> x_1: Text
  -> BinahRecord < 
       {\row -> userName (entityVal row) == x_0 && userSsn (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> (entityKey viewer == entityKey row)}
     > User
@-}
mkUser x_0 x_1 = BinahRecord (User x_0 x_1)

{-@ invariant {v: Entity User | v == getJust (entityKey v)} @-}



{-@ assume userId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
userId' :: EntityFieldWrapper User UserId
userId' = EntityFieldWrapper UserId

{-@ assume userName' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == userName (entityVal row)}
  , {\field row  -> field == userName (entityVal row)}
  > _ _
@-}
userName' :: EntityFieldWrapper User Text
userName' = EntityFieldWrapper UserName

{-@ assume userSsn' :: EntityFieldWrapper <
    {\user viewer -> entityKey viewer == entityKey user}
  , {\row field  -> field == userSsn (entityVal row)}
  , {\field row  -> field == userSsn (entityVal row)}
  > _ _
@-}
userSsn' :: EntityFieldWrapper User Text
userSsn' = EntityFieldWrapper UserSsn

-- * TodoItem

{-@ measure todoItemOwner :: TodoItem -> UserId @-}
{-@ measure todoItemTask :: TodoItem -> Text @-}

{-@ mkTodoItem :: 
     x_0: UserId
  -> x_1: Text
  -> BinahRecord < 
       {\row -> todoItemOwner (entityVal row) == x_0 && todoItemTask (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> (shared (todoItemOwner (entityVal row)) (entityKey viewer))}
     > TodoItem
@-}
mkTodoItem x_0 x_1 = BinahRecord (TodoItem x_0 x_1)

{-@ invariant {v: Entity TodoItem | v == getJust (entityKey v)} @-}



{-@ assume todoItemId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
todoItemId' :: EntityFieldWrapper TodoItem TodoItemId
todoItemId' = EntityFieldWrapper TodoItemId

{-@ assume todoItemOwner' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == todoItemOwner (entityVal row)}
  , {\field row  -> field == todoItemOwner (entityVal row)}
  > _ _
@-}
todoItemOwner' :: EntityFieldWrapper TodoItem UserId
todoItemOwner' = EntityFieldWrapper TodoItemOwner

{-@ assume todoItemTask' :: EntityFieldWrapper <
    {\item viewer -> shared (todoItemOwner (entityVal item)) (entityKey viewer)}
  , {\row field  -> field == todoItemTask (entityVal row)}
  , {\field row  -> field == todoItemTask (entityVal row)}
  > _ _
@-}
todoItemTask' :: EntityFieldWrapper TodoItem Text
todoItemTask' = EntityFieldWrapper TodoItemTask

-- * Share

{-@ measure shareFrom :: Share -> UserId @-}
{-@ measure shareTo :: Share -> UserId @-}

{-@ mkShare :: 
     x_0: UserId
  -> x_1: UserId
  -> BinahRecord < 
       {\row -> shareFrom (entityVal row) == x_0 && shareTo (entityVal row) == x_1}
     , {\_ _ -> True}
     , {\row viewer -> False}
     > Share
@-}
mkShare x_0 x_1 = BinahRecord (Share x_0 x_1)

{-@ invariant {v: Entity Share | v == getJust (entityKey v)} @-}

{-@ invariant {v: Entity Share | shared (shareFrom (entityVal v)) (shareTo (entityVal v))} @-}

{-@ assume shareId' :: EntityFieldWrapper <
    {\row viewer -> True}
  , {\row field  -> field == entityKey row}
  , {\field row  -> field == entityKey row}
  > _ _
@-}
shareId' :: EntityFieldWrapper Share ShareId
shareId' = EntityFieldWrapper ShareId

{-@ assume shareFrom' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == shareFrom (entityVal row)}
  , {\field row  -> field == shareFrom (entityVal row)}
  > _ _
@-}
shareFrom' :: EntityFieldWrapper Share UserId
shareFrom' = EntityFieldWrapper ShareFrom

{-@ assume shareTo' :: EntityFieldWrapper <
    {\_ _ -> True}
  , {\row field  -> field == shareTo (entityVal row)}
  , {\field row  -> field == shareTo (entityVal row)}
  > _ _
@-}
shareTo' :: EntityFieldWrapper Share UserId
shareTo' = EntityFieldWrapper ShareTo

--------------------------------------------------------------------------------
-- | Inline
--------------------------------------------------------------------------------


