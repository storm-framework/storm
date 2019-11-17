{-# LANGUAGE OverloadedStrings #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Tests where
import Data.Functor.Identity (Identity)
import Control.Monad.Reader (ReaderT)
import Database.Persist.Sql (SqlBackend)
import Data.Text (Text)

import Core
import Model
import Infrastructure
import Filters
import Actions


-- | Projection test
{-@ projectUserId :: user:(Entity User) -> TaggedT<{\_ -> True}, {\_ -> False}> Identity {v:UserId | v == entityKey user}  @-}
projectUserId :: Entity User -> TaggedT Identity UserId
projectUserId = project userIdField

{-@ projectUserName :: user:{Entity User | entityKey user == id1} -> TaggedT<{\viewer -> entityKey viewer == id1}, {\_ -> False}> Identity {v:Text | v == userName (entityVal user)}  @-}
projectUserName :: Entity User -> TaggedT Identity Text
projectUserName = project userNameField

{-@ projectUserSsn :: user:{Entity User | entityKey user == id1} -> TaggedT<{\viewer -> entityKey viewer == id1}, {\_ -> False}> Identity {v:Text | v == userSsn (entityVal user) && tlen v == 9}  @-}
projectUserSsn :: Entity User -> TaggedT Identity Text
projectUserSsn = project userSsnField

{-@ measure Tests.id1 :: UserId @-}
{-@ assume id1 :: {v:UserId | v == id1} @-}
id1 :: UserId
id1 = undefined

-- {-@ measure Tests.aliceText :: Text @-}
-- {-@ assume aliceText :: {v:Text | v == aliceText} @-}
-- aliceText :: Text
-- aliceText = "alice"

-- {-@ combinatorExample1 :: Filter<{\row v -> entityKey v == entityKey row}, {\row -> userName (entityVal row) == aliceText}> User @-}
-- combinatorExample1 :: Filter User
-- combinatorExample1 = userNameField ==. aliceText

-- {-@ exampleList1 :: Filter<{\_ -> True}, {\_ -> True}> User @-}
-- exampleList1 :: Filter User
-- exampleList1 = trueF

-- -- {-@ exampleList2 :: Filter<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1}> User @-}
-- -- exampleList2 :: Filter User
-- -- exampleList2 = (userFriendField ==. id1)

-- -- {-@ exampleList3 :: Filter<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- -- exampleList3 :: Filter User
-- -- exampleList3 = userNameField ==. "alice" &&: userFriendField ==. id1

-- -- {-@ exampleList4 :: Filter<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- -- exampleList4 :: Filter User
-- -- exampleList4 = userFriendField ==. id1 &&: userNameField ==. "alice"

-- {-@ exampleList5 :: Filter<{\row v -> entityKey v == entityKey row}, {\user -> userName (entityVal user) == "alice"}> User @-}
-- exampleList5 :: Filter User
-- exampleList5 = userNameField ==. "alice"

-- -- {-@ exampleSelectList1 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : Entity User | userFriend (entityVal v) == id1}] @-}
-- -- exampleSelectList1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- -- exampleSelectList1 = selectList filters
-- --   where
-- --     {-@ filters :: Filter<{\_ v -> entityKey v == id1}, {\v -> userFriend (entityVal v) == id1}> User @-}
-- --     filters = userFriendField ==. id1

-- -- {-@ exampleSelectList2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : _ | userFriend (entityVal v) == id1 && userName (entityVal v) == "alice"}] @-}
-- -- exampleSelectList2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- -- exampleSelectList2 = selectList (userNameField ==. "alice" &&: userFriendField ==. id1)

-- {-@ exampleSelectList3 :: TaggedT<{\_ -> False}, {\_ -> False}> _ [{v : _ | userName (entityVal v) == "alice"}] @-}
-- exampleSelectList3 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- exampleSelectList3 = selectList (userNameField ==. "alice")

-- -- {-@ projectSelect1 :: [{v:_ | userFriend (entityVal v) == id1}] -> TaggedT<{\_ -> False}, {\_ -> False}> Identity [{v:_ | len v == 9}] @-}
-- -- projectSelect1 :: [Entity User] -> TaggedT Identity [String]
-- -- projectSelect1 users = projectList userSSNField users

-- -- -- | This is fine: user 1 can see both the filtered rows and the name field in
-- -- --   each of these rows
-- -- {-@ names :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [String] @-}
-- -- names :: TaggedT (ReaderT SqlBackend TIO) [String]
-- -- names = do
-- --   rows <- selectList (userFriendField ==. id1)
-- --   projectList userNameField rows

-- -- -- | This is bad: the result of the query is not public
-- -- {-@ bad1 :: TaggedT<{\v -> True}, {\_ -> False}> _ [{v: _ | userFriend (entityVal v) == id1}]
-- -- @-}
-- -- bad1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- -- bad1 = selectList (userFriendField ==. id1)

-- -- | This is bad: who knows who else has name "alice" and is not friends with user 1?
-- {-@ bad2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v: _ | userName (entityVal v) == "alice"}]
-- @-}
-- bad2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- bad2 = selectList (userNameField ==. "alice")

-- -- -- | This is bad: user 1 can see the filtered rows but not their SSNs
-- -- {-@ badSSNs :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v:_ | len v == 9}]
-- -- @-}
-- -- badSSNs :: TaggedT (ReaderT SqlBackend TIO) [String]
-- -- badSSNs = do
-- --   rows <- selectList (userFriendField ==. id1)
-- --   projectList userSSNField rows -- bad

-- {-@
-- getSharedTasks :: u:_ -> TaggedT<{\viewer -> entityKey viewer == u}, {\_ -> False}> _ [{v:_ | len v > 0}]
-- @-}
-- getSharedTasks :: Key User -> TaggedT (ReaderT SqlBackend TIO) [Text]
-- getSharedTasks userKey = do
--   shares <- selectList (shareToField ==. userKey)
--   sharedFromUsers <- projectList shareFromField shares
--   sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers)
--   projectList todoItemTaskField sharedTodoItems

-- {-@
-- preserveInvariant :: TaggedT<{\viewer -> True}, {\_ -> False}> _ [Entity {s:Share | shared (shareFrom s) (shareTo s)}]
-- @-}
-- preserveInvariant :: TaggedT (ReaderT SqlBackend TIO) [Entity Share]
-- preserveInvariant = selectList filters
--   where
--     {-@ filters :: Filter<{\_ _ -> True}, {\_ -> True}> {s:Share | shared (shareFrom s) (shareTo s)} @-}
--     filters :: Filter Share
--     filters = trueF

-- {-@ action1 :: TaggedT<{\viewer -> False}, {\recipient -> False}> _ _ @-}
-- action1 :: TaggedT TIO ()
-- action1 = undefined

-- {-@ action2 :: _ -> TaggedT<{\viewer -> True}, {\recipient -> True}> _ _ @-}
-- action2 :: a -> TaggedT TIO a
-- action2 = undefined

-- {-@ action3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- action3 :: TaggedT TIO ()
-- action3 = undefined

-- {-@ testBind1 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- testBind1 = action1 >>= action2 -- bad

-- {-@ testBind2 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- testBind2 = action3 >>= \_ -> action3 -- bad

-- {-@ testBind3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- testBind3 = action3 >> action3

-- {-@
-- getSharedTasksBad :: _ -> TaggedT<{\viewer -> True}, {\_ -> False}> _ _
-- @-}
-- getSharedTasksBad :: Key User -> TaggedT (ReaderT SqlBackend TIO) [Text]
-- getSharedTasksBad userKey = do
--   shares <- selectList trueF
--   sharedFromUsers <- projectList shareFromField shares
--   sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers)
--   projectList todoItemTaskField sharedTodoItems -- bad

-- {-@ consumeTagged :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. TaggedT<label, clear> m a -> b @-}
-- consumeTagged :: TaggedT m a -> b
-- consumeTagged _ = undefined

-- {-@ ignore specialReturn @-}
-- {-@ assume specialReturn :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a @-}
-- specialReturn :: Monad m => a -> TaggedT m a
-- specialReturn = return -- TODO: why does normal return not work?

-- {-@ printSharedTasks'' :: u:_ -> Filter<{\sh -> shareTo (entityVal sh) == entityKey u}, {\_ _ -> False}> _ @-}
-- printSharedTasks'' :: Entity User -> Filter Share
-- printSharedTasks'' user = shareToField ==. entityKey user

-- {-@ printSharedTasks' :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ [{v: Entity Share | shareTo (entityVal v) == entityKey u}] @-}
-- printSharedTasks' :: Entity User -> TaggedT (ReaderT SqlBackend TIO) [Entity Share]
-- printSharedTasks' user = do
--   selectList (shareToField ==. entityKey user)


-- {-@ printSharedTasks :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- printSharedTasks :: Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
-- printSharedTasks user = do
--   shares <- selectList (shareToField ==. entityKey user)
--   sharedFromUsers <- projectList shareFromField shares
--   sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers)
--   tasks <- projectList todoItemTaskField sharedTodoItems
--   printTo user $ show tasks

-- {-@ printSharedTasksBad :: _ -> _ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
-- printSharedTasksBad :: Entity User -> Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
-- printSharedTasksBad user1 user2 = do
--   shares <- selectList (shareToField ==. entityKey user1)
--   sharedFromUsers <- projectList shareFromField shares
--   sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers)
--   tasks <- projectList todoItemTaskField sharedTodoItems -- bad
--   printTo user2 $ show tasks -- bad


