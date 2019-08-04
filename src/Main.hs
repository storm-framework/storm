{-# LANGUAGE FlexibleContexts, OverloadedStrings, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, GADTs, TypeFamilies, GeneralizedNewtypeDeriving, PartialTypeSignatures, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses #-}
{-@ LIQUID "--no-pattern-inline" @-}
module Main where

import Data.Functor.Const
import Data.Text (Text)
import Data.Aeson (ToJSON, FromJSON)
import Database.Persist hiding ((==.), (<-.), selectList, selectFirst, insert, entityKey, entityVal) --(PersistField, PersistValue, PersistEntity, Key, EntityField, Unique, Filter, fieldLens, Entity(Entity))
import qualified Database.Persist
import qualified Database.Persist.Sqlite
import qualified Database.Persist.TH
import qualified Data.Text
import qualified Data.Proxy
import qualified GHC.Int
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Data.Functor.Identity (Identity)
import Database.Persist.TH (mkPersist, sqlSettings, persistLowerCase)
import Database.Persist.Sql (SqlBackend, Migration)

import Data.Maybe (fromJust)

import Core
import Model
import Infrastructure
import Filters
import Actions


-- * Client code

runSqlite :: Text -> ReaderT SqlBackend TIO a -> TIO a
runSqlite connStr action = TIO . Database.Persist.Sqlite.runSqlite connStr $ do
  backend <- ask
  liftIO . runTIO . (`runReaderT` backend) $ action

runMigration :: (MonadTIO m, MonadReader SqlBackend m) => Migration -> m ()
runMigration migration = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Database.Persist.Sqlite.runMigration migration

insert :: (PersistStoreWrite backend, PersistRecordBackend record backend, MonadTIO m, MonadReader backend m) => record -> m (Key record)
insert record = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Database.Persist.insert record

-- TODO: Remove the Sqlite stuff from main once mapTaggedT gets worked out
{-@ ignore main @-}
main :: IO ()
main = runTIO . unTag . mapTaggedT (runSqlite ":memory:") $ taggedMain

setupDB :: ReaderT SqlBackend TIO (UserId, UserId)
setupDB = do
  runMigration migrateAll

  aliceId <- insert $ User "Alice" "123456789"
  bobId <- insert $ User "Bob" "987654321"

  insert $ TodoItem bobId "Get groceries"
  insert $ TodoItem bobId "Vacuum"
  insert $ TodoItem aliceId "Submit paper"

  insert $ Share bobId aliceId

  return (aliceId, bobId)

{-@ taggedMain :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
taggedMain ::  TaggedT (ReaderT SqlBackend TIO) ()
taggedMain = do
  (aliceId, bobId) <- lift setupDB
  printSharedWith aliceId
  printSharedWith bobId

{-@ printSharedWith :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
printSharedWith :: UserId -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedWith userId = do
  user <- fromJust <$> selectFirst (userIdField ==. userId ?: Empty)
  shares <- selectList (shareToField ==. entityKey user ?: Empty)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  tasks <- projectList todoItemTaskField sharedTodoItems
  printTo user $ show tasks
