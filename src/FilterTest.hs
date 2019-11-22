module FilterTest where

import Binah.Core
import Binah.Filters
import Model

{-@ measure userId :: UserId @-}
{-@ userId :: {v:_ | v == userId} @-}
userId :: UserId
userId = undefined

{-@ test1Good :: Filter<{\_ _ -> True}, {\_ -> True}> _ @-}
test1Good :: Filter User
test1Good = trueF -- good

{-@ test1Bad :: Filter<{\_ _ -> True}, {\_ -> False}> _ @-}
test1Bad :: Filter User
test1Bad = trueF -- bad

{-@ test2Good :: Filter<{\_ _ -> True}, {\_ -> True}> _ @-}
test2Good :: Filter User
test2Good = userIdField ==. userId -- good

{-@ test2Bad :: Filter<{\_ _ -> True}, {\_ -> True}> _ @-}
test2Bad :: Filter User
test2Bad = userIdField ==. userId -- bad
