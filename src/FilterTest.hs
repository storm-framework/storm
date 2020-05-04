module FilterTest where

import Binah.Core
import Binah.Filters
import Model

{-@ measure userId :: UserId @-}
{-@ userId :: {v:_ | v == userId} @-}
userId :: UserId
userId = undefined

{-@ test1Good :: Filter<{\_ _ -> True}, {\_ -> True}> _ _ @-}
test1Good :: Filter (Entity User) User
test1Good = trueF -- good

{-@ test1Bad :: Filter<{\_ _ -> True}, {\_ -> False}> _ _ @-}
test1Bad :: Filter (Entity User) User
test1Bad = trueF -- bad

{-@ test2Good :: Filter<{\_ _ -> True}, {\_ -> True}> _ _ @-}
test2Good :: Filter (Entity User) User
test2Good = userIdField ==. userId -- good

{-@ test2Bad :: Filter<{\_ _ -> True}, {\_ -> True}> _ _ @-}
test2Bad :: Filter (Entity User) User
test2Bad = userIdField ==. userId -- bad
