{-@ LIQUID "--no-pattern-inline" @-}

module Tests where
import Control.Monad.Reader (ReaderT)
import Database.Persist.Sql (SqlBackend)

import Core
import Model
import Infrastructure
import Filters
import Actions


{-@ measure Tests.id1 :: Key User @-}
{-@ assume id1 :: {v:Key User | v == id1} @-}
id1 :: Key User
id1 = UserKey undefined

{-@ combinatorExample1 :: Filter<{\row -> userName (entityVal row) == "alice"}, {\row v -> entityKey v == entityKey row}> User @-}
combinatorExample1 :: Filter User
combinatorExample1 = userNameField ==. "alice"

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = nilFL

-- {-@ exampleList2 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1}> User @-}
-- exampleList2 :: FilterList User
-- exampleList2 = (userFriendField ==. id1) ?: nilFL

-- {-@ exampleList3 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- exampleList3 :: FilterList User
-- exampleList3 = userNameField ==. "alice" ?: userFriendField ==. id1 ?: nilFL

-- {-@ exampleList4 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- exampleList4 :: FilterList User
-- exampleList4 = userFriendField ==. id1 ?: userNameField ==. "alice" ?: nilFL

{-@ exampleList5 :: FilterList<{\row v -> entityKey v == entityKey row}, {\user -> userName (entityVal user) == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = userNameField ==. "alice" ?: nilFL

-- {-@ exampleSelectList1 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : Entity User | userFriend (entityVal v) == id1}] @-}
-- exampleSelectList1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- exampleSelectList1 = selectList filters
--   where
--     {-@ filters :: FilterList<{\_ v -> entityKey v == id1}, {\v -> userFriend (entityVal v) == id1}> User @-}
--     filters = userFriendField ==. id1 ?: nilFL

-- {-@ exampleSelectList2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : _ | userFriend (entityVal v) == id1 && userName (entityVal v) == "alice"}] @-}
-- exampleSelectList2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- exampleSelectList2 = selectList (userNameField ==. "alice" ?: userFriendField ==. id1 ?: nilFL)

{-@ exampleSelectList3 :: TaggedT<{\_ -> False}, {\_ -> False}> _ [{v : _ | userName (entityVal v) == "alice"}] @-}
exampleSelectList3 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
exampleSelectList3 = selectList (userNameField ==. "alice" ?: nilFL)

-- {-@ projectSelect1 :: [{v:_ | userFriend (entityVal v) == id1}] -> TaggedT<{\_ -> False}, {\_ -> False}> Identity [{v:_ | len v == 9}] @-}
-- projectSelect1 :: [Entity User] -> TaggedT Identity [String]
-- projectSelect1 users = projectList userSSNField users

-- -- | This is fine: user 1 can see both the filtered rows and the name field in
-- --   each of these rows
-- {-@ names :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [String] @-}
-- names :: TaggedT (ReaderT SqlBackend TIO) [String]
-- names = do
--   rows <- selectList (userFriendField ==. id1 ?: nilFL)
--   projectList userNameField rows

-- -- | This is bad: the result of the query is not public
-- {-@ bad1 :: TaggedT<{\v -> True}, {\_ -> False}> _ [{v: _ | userFriend (entityVal v) == id1}]
-- @-}
-- bad1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- bad1 = selectList (userFriendField ==. id1 ?: nilFL)

-- | This is bad: who knows who else has name "alice" and is not friends with user 1?
{-@ bad2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v: _ | userName (entityVal v) == "alice"}]
@-}
bad2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
bad2 = selectList (userNameField ==. "alice" ?: nilFL)

-- -- | This is bad: user 1 can see the filtered rows but not their SSNs
-- {-@ badSSNs :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v:_ | len v == 9}]
-- @-}
-- badSSNs :: TaggedT (ReaderT SqlBackend TIO) [String]
-- badSSNs = do
--   rows <- selectList (userFriendField ==. id1 ?: nilFL)
--   projectList userSSNField rows -- bad

{-@
getSharedTasks :: u:_ -> TaggedT<{\viewer -> entityKey viewer == u}, {\_ -> False}> _ [{v:_ | len v > 0}]
@-}
getSharedTasks :: Key User -> TaggedT (ReaderT SqlBackend TIO) [String]
getSharedTasks userKey = do
  shares <- selectList (shareToField ==. userKey ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  projectList todoItemTaskField sharedTodoItems

{-@
preserveInvariant :: TaggedT<{\viewer -> True}, {\_ -> False}> _ [Entity {s:Share | shared (shareFrom s) (shareTo s)}]
@-}
preserveInvariant :: TaggedT (ReaderT SqlBackend TIO) [Entity Share]
preserveInvariant = selectList filters
  where
    {-@ filters :: FilterList<{\_ _ -> True}, {\_ -> True}> {s:Share | shared (shareFrom s) (shareTo s)} @-}
    filters :: FilterList Share
    filters = nilFL

{-@ action1 :: TaggedT<{\viewer -> False}, {\recipient -> False}> _ _ @-}
action1 :: TaggedT TIO ()
action1 = undefined

{-@ action2 :: _ -> TaggedT<{\viewer -> True}, {\recipient -> True}> _ _ @-}
action2 :: a -> TaggedT TIO a
action2 = undefined

{-@ action3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
action3 :: TaggedT TIO ()
action3 = undefined

{-@ testBind1 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind1 = action1 >>= action2 -- bad

{-@ testBind2 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind2 = action3 >>= \_ -> action3 -- bad

{-@ testBind3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind3 = action3 >> action3

{-@
getSharedTasksBad :: _ -> TaggedT<{\viewer -> True}, {\_ -> False}> _ _
@-}
getSharedTasksBad :: Key User -> TaggedT (ReaderT SqlBackend TIO) [String]
getSharedTasksBad userKey = do
  shares <- selectList nilFL
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  projectList todoItemTaskField sharedTodoItems -- bad

{-@ consumeTagged :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. TaggedT<label, clear> m a -> b @-}
consumeTagged :: TaggedT m a -> b
consumeTagged _ = undefined

{-@ ignore specialReturn @-}
{-@ assume specialReturn :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a @-}
specialReturn :: Monad m => a -> TaggedT m a
specialReturn = return -- TODO: why does normal return not work?

{-@ printSharedTasks'' :: u:_ -> Filter<{\sh -> shareTo (entityVal sh) == entityKey u}, {\_ _ -> False}> _ @-}
printSharedTasks'' :: Entity User -> Filter Share
printSharedTasks'' user = shareToField ==. entityKey user

{-@ printSharedTasks' :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ [{v: Entity Share | shareTo (entityVal v) == entityKey u}] @-}
printSharedTasks' :: Entity User -> TaggedT (ReaderT SqlBackend TIO) [Entity Share]
printSharedTasks' user = do
  selectList (shareToField ==. entityKey user ?: nilFL)


{-@ printSharedTasks :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
printSharedTasks :: Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedTasks user = do
  shares <- selectList (shareToField ==. entityKey user ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  tasks <- projectList todoItemTaskField sharedTodoItems
  printTo user $ show tasks

{-@ printSharedTasksBad :: _ -> _ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
printSharedTasksBad :: Entity User -> Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedTasksBad user1 user2 = do
  shares <- selectList (shareToField ==. entityKey user1 ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  tasks <- projectList todoItemTaskField sharedTodoItems -- bad
  printTo user2 $ show tasks -- bad

