{-# LANGUAGE GADTs #-}
module Binah.Insert where

import           Binah.Infrastructure
import qualified Frankie.Log
import           Control.Monad.Reader           ( MonadReader(..)
                                                , runReaderT
                                                )
import qualified Database.Persist              as Persist
import           Control.Exception              (SomeException)
import           Control.Monad.Catch
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
      |- {v: (Entity<querypolicy rec> User) | True} <: {v: (Entity<audience> User) | True}
  }

  BinahRecord<p, insertpolicy, querypolicy> record -> TaggedT<{\_ -> True}, audience> m (Key record)
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

{-@ ignore insertMaybe @-}
{-@
assume insertMaybe :: forall < p :: Entity record -> Bool
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

  BinahRecord<p, insertpolicy, querypolicy> record -> TaggedT<{\_ -> True}, audience> _ (Maybe (Key record))
@-}
insertMaybe
  :: ( MonadTIO m
     , Persist.PersistStoreWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => BinahRecord record
  -> TaggedT m (Maybe (Key record))
insertMaybe record = do
  backend <- ask
  liftTIO . TIO $ runReaderT act  backend
  where
    act = (Just <$> Persist.insert (persistentRecord record)) 
            `catch` 
              (\(SomeException e) -> return Nothing)

{-@ ignore insertOrMsg @-}
{-@
assume insertOrMsg :: forall < p :: Entity record -> Bool
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
  String -> BinahRecord<p, insertpolicy, querypolicy> record -> TaggedT<{\_ -> True}, audience> _ (Maybe (Key record))
@-}
insertOrMsg
  :: ( MonadTIO m
     , Persist.PersistStoreWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => String 
  -> BinahRecord record
  -> TaggedT m (Maybe (Key record))
insertOrMsg msg row = do 
  res <- insertMaybe row 
  case res of 
    Nothing -> Frankie.Log.log Frankie.Log.ERROR msg
    _       -> return ()
  return res

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
      |- {v: (Entity<querypolicy rec> User) | True} <: {v: (Entity<audience> User) | True}
  }

  [BinahRecord<p, insertpolicy, querypolicy> record]
  -> TaggedT<{\_ -> True}, audience> m [Key record]
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
