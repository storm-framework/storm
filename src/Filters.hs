-- | Filters for every field / operation combination.

module Filters
  ( Filter
  , userNameEq, userSsnEq, userFriendEq
  ) where

import qualified Database.Persist
import Database.Persist ((==.))
import Model

{-@ data Filter record <r :: Entity record -> Bool, q :: Entity record -> User -> Bool> = Filter _ @-}
{-@ data variance Filter covariant covariant contravariant @-}
data Filter record = Filter (Database.Persist.Filter record)

{-@ assume userNameEq :: val:String -> Filter<{\row -> userName (entityVal row) == val}, {\row v -> entityKey v = userFriend (entityVal row)}> User @-}
userNameEq :: String -> Filter User
userNameEq val = Filter (UserName ==. val)

{-@ assume userSsnEq :: val:Int -> RefinedFilter<{\row -> userSsn (entityVal row) == val}, {\row v -> entityKey v = userId (entityVal row)}> User @-}
userSsnEq :: Int -> Filter User
userSsnEq val = Filter (UserSsn ==. val)

{-@ assume userFriendEq :: val:Int -> RefinedFilter<{\row -> userFriend (entityVal row) == val}, {\row v -> entityKey v = userFriend (entityVal row)}> User @-}
userFriendEq :: UserId -> Filter User
userFriendEq val = Filter (UserFriend ==. val)
