{-# LANGUAGE GADTs #-}
module Binah.Insert where


import           Binah.Infrastructure
import           Data.Text
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
                        , level    :: Entity User -> Bool
                        , audience :: Entity User -> Bool
                        >.
  { rec :: (Entity<p> record) |- {v: (Entity<level> User) | True} <: {v: (Entity<insertpolicy rec> User) | True}}

  { rec :: (Entity<p> record) |- {v: (Entity<querypolicy p> User) | True} <: {v: (Entity<audience> User) | True}}

  BinahRecord<p, insertpolicy, querypolicy> record -> TaggedT<level, audience> _ (Key record)
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
