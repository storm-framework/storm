-- | Example client code.
module Client where

import BinahPrelude
import Database.Persist (Entity)

aliceId :: UserId
aliceId = undefined

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = Empty

{-@ exampleList2 :: FilterList<{\_ v -> entityKey v == aliceId}, {\user -> userFriend (entityVal user) == aliceId}> User @-}
exampleList2 :: FilterList User
exampleList2 = userFriendEq aliceId ?: Empty

{-@ exampleList3 :: FilterList<{\_ v -> entityKey v == aliceId}, {\user -> userFriend (entityVal user) == aliceId && userName (entityVal user) == "alice"}> User @-}
exampleList3 :: FilterList User
exampleList3 = userNameEq "alice" ?: userFriendEq aliceId ?: Empty

{-@ exampleList4 :: FilterList<{\_ v -> entityKey v == aliceId}, {\user -> userFriend (entityVal user) == aliceId && userName (entityVal user) == "alice"}> User @-}
exampleList4 :: FilterList User
exampleList4 = userFriendEq aliceId ?: userNameEq "alice" ?: Empty

{-@ exampleList5 :: FilterList<{\row v -> entityKey v == userFriend row}, {\user -> userName (entityVal user) == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = userNameEq "alice" ?: Empty

{-@ exampleSelectList1 :: Tagged<{\v -> entityKey v == aliceId}> [{v : User | userFriend (entityVal v) == aliceId}] @-}
exampleSelectList1 :: Tagged [Entity User]
exampleSelectList1 = selectList (userFriendEq aliceId ?: Empty)

{-@ exampleSelectList2 :: Tagged<{\v -> entityKey v == aliceId}> [{v : User | userFriend (entityVal v) == aliceId && userName (entityVal v) == "alice"}] @-}
exampleSelectList2 :: Tagged [Entity User]
exampleSelectList2 = selectList (userNameEq "alice" ?: userFriendEq aliceId ?: Empty)

{-@ exampleSelectList3 :: Tagged<{\v -> False}> [{v : User | userName (entityVal v) == "alice"}] @-}
exampleSelectList3 :: Tagged [Entity User]
exampleSelectList3 = selectList (userNameEq "alice" ?: Empty)

-- | This is fine: user aliceId can see both the filtered rows and the name field in
--   each of these rows
{-@ names :: Tagged<{\v -> entityKey v == aliceId}> [String]
@-}
names :: Tagged [String]
names = do
  rows <- selectList (userFriendEq aliceId ?: Empty)
  projectList rows UserName

-- | This is bad: the result of the query is not public
{-@ bad1 :: Tagged<{\v -> true}> [{v: User | userFriend (entityVal v) == aliceId}]
@-}
bad1 :: Tagged [Entity User]
bad1 = selectList (userFriendEq aliceId ?: Empty)

-- | This is bad: who knows who else has name "alice" and is not friends with user aliceId?
{-@ bad2 :: Tagged<{\v -> entityKey v == aliceId}> [{v: User | userName (entityVal v) == "alice"}]
@-}
bad2 :: Tagged [Entity User]
bad2 = selectList (userNameEq "alice" ?: Empty)

-- | This is bad: user aliceId can see the filtered rows but not their SSNs
{-@ badSSNs :: Tagged<{\v -> entityKey v == aliceId}> [Int]
@-}
badSSNs :: Tagged [Int]
badSSNs = do
  rows <- selectList (userFriendEq aliceId ?: Empty)
  projectList rows UserSsn
