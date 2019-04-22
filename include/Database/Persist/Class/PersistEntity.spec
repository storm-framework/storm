module spec Database.Persist.Class.PersistEntity where

entityKey :: e:Database.Persist.Class.PersistEntity.Entity record -> {v:Database.Persist.Class.PersistEntity.Key record | v == entityKey e}
entityVal :: e:Database.Persist.Class.PersistEntity.Entity record -> {v:record | v == entityVal e}
