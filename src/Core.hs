module Core
  ( entityKey
  , entityVal
  ) where

import qualified Database.Persist as Persist

{-@ measure entityKey :: Entity record -> Key record @-}
{-@ assume entityKey :: entity:_ -> {v:_ | v == entityKey entity} @-}
entityKey = Persist.entityKey

{-@ measure entityVal :: Entity record -> record @-}
{-@ assume entityVal :: entity:_ -> {v:_ | v == entityVal entity} @-}
entityVal = Persist.entityVal
