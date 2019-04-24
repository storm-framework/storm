module spec Database.Persist.Class.PersistEntity where

measure entityKey :: e:Database.Persist.Class.PersistEntity.Entity record -> {v:Database.Persist.Class.PersistEntity.Key record | v == entityKey e}
measure entityVal :: e:Database.Persist.Class.PersistEntity.Entity record -> {v:record | v == entityVal e}
