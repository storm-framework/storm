{-# LANGUAGE GADTs #-}
module Binah.Insert where


import           Binah.Infrastructure
import           Control.Monad.Reader           ( MonadReader(..)
                                                , runReaderT
                                                )
import qualified Database.Persist              as Persist

import           Binah.Core
import           Model

{-@ ignore insert @-}
{-@
assume insert :: forall < p :: Entity record -> Bool
                        , insertpolicy :: Entity record -> Entity User -> Bool
                        , querypolicy  :: Entity record -> Entity User -> Bool
                        , audience :: Entity User -> Bool
                        >.
  { rec :: (Entity<p> record)
      |- {v: (Entity User) | v == currentUser} <: {v: (Entity<insertpolicy rec> User) | True}
  }

  { rec :: (Entity<p> record)
      |- {v: (Entity<querypolicy p> User) | True} <: {v: (Entity<audience> User) | True}
  }

  BinahRecord<p, insertpolicy, querypolicy> record -> TaggedT<{\_ -> True}, audience> _ (Key record)
@-}
insert
  :: ( MonadTIO m
     , Persist.PersistStoreWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => BinahRecord record
  -> TaggedT m (Key record)
insert record = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.insert (persistentRecord record)) backend

{-@ ignore insertMany @-}
{-@
assume insertMany :: forall < p :: Entity record -> Bool
                            , insertpolicy :: Entity record -> Entity User -> Bool
                            , querypolicy  :: Entity record -> Entity User -> Bool
                            , audience :: Entity User -> Bool
                            >.
  { rec :: (Entity<p> record)
      |- {v: (Entity User) | v == currentUser} <: {v: (Entity<insertpolicy rec> User) | True}
  }

  { rec :: (Entity<p> record)
      |- {v: (Entity<querypolicy p> User) | True} <: {v: (Entity<audience> User) | True}
  }

  [BinahRecord<p, insertpolicy, querypolicy> record]
  -> TaggedT<{\_ -> True}, audience> _ [Key record]
@-}
insertMany
  :: ( MonadTIO m
     , Persist.PersistStoreWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => [BinahRecord record]
  -> TaggedT m [Key record]
insertMany records = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.insertMany (map persistentRecord records)) backend
