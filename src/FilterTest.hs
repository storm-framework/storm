module FilterTest where

import Core
import Model
import Filters

{-@ measure userId :: UserId @-}
{-@ userId :: {v:_ | v == userId} @-}
userId :: UserId
userId = undefined

{-@ test1Good :: FilterList<{\_ -> True}, {\_ -> True}> _ @-}
test1Good :: FilterList User
test1Good = nilFL -- good

{-@ test1Bad :: FilterList<{\_ -> True}, {\_ -> False}> _ @-}
test1Bad :: FilterList User
test1Bad = nilFL -- bad

{-@ test2Good :: FilterList<{\_ -> }, {\_ -> True}> _ @-}
test2Good :: FilterList User
test2Good = userIdField ==. userId ?: nilFL -- good

{-@ test2Bad :: FilterList<{\_ -> True}, {\_ -> True}> _ @-}
test2Bad :: FilterList User
test2Bad = userIdField ==. userId ?: nilFL -- bad
