{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Main where

import Data.Maybe (fromJust)
import Data.Text (Text)
import Control.Exception (try, evaluate)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), withReaderT)
import Database.Persist.Sqlite (SqlBackend, Migration, runMigration, runSqlite)
import Database.Persist (PersistStoreWrite, PersistRecordBackend, insert)

import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Text.Encoding as Text
import qualified Text.Mustache as Mustache
import Text.Mustache ((~>), ToMustache(..))
import qualified Text.Mustache.Types as Mustache
import Control.Concurrent.MVar
import qualified Data.HashMap.Strict as HashMap
import Frankie.Config
import Frankie.Auth

import Binah.Core
import Binah.Infrastructure
import Binah.Filters
import Binah.Actions
import Binah.Frankie
import Binah.Templates
import Binah.Updates
import Model

-- * Client code

data Config = Config
  { configBackend :: !SqlBackend
  , configAliceId :: !UserId
  , configBobId :: !UserId
  , configTemplateCache :: !(MVar Mustache.TemplateCache)
  , configAuthMethod :: !(AuthMethod (Entity User) Controller)
  }

instance HasSqlBackend Config where
  getSqlBackend = configBackend

instance HasTemplateCache Config where
  getTemplateCache = configTemplateCache

instance HasAuthMethod (Entity User) Controller Config where
  getAuthMethod = configAuthMethod

data Overview = Overview
  { overviewUsername :: Text
  , overviewSharedTasks :: [Text]
  }

instance TemplateData Overview where
  templateFile = "overview.html.mustache"

instance ToMustache Overview where
  toMustache (Overview username tasks) = Mustache.object
    [ "username" ~> toMustache username
    , "sharedTasks" ~> toMustache (map (\task -> Mustache.object ["text" ~> task]) tasks)
    ]


getBackend :: MonadConfig Config m => m SqlBackend
getBackend = configBackend <$> getConfig

getAliceId :: MonadConfig Config m => m UserId
getAliceId = configAliceId <$> getConfig

getBobId :: MonadConfig Config m => m UserId
getBobId = configBobId <$> getConfig

setup :: MonadIO m => ReaderT SqlBackend m Config
setup = do
  templateCache <- liftIO $ newMVar mempty

  runMigration migrateAll

  aliceId <- insert $ User "Alice" "123456789"
  bobId <- insert $ User "Bob" "987654321"

  insert $ TodoItem bobId "Get groceries"
  insert $ TodoItem bobId "Submit paper"
  insert $ TodoItem aliceId "Research"

  insert $ Share bobId aliceId

  backend <- ask

  return $  Config
    { configBackend = backend
    , configAliceId = aliceId
    , configBobId = bobId
    , configTemplateCache = templateCache
    , configAuthMethod = httpAuthDb
    }

type Controller = TaggedT (ReaderT SqlBackend (ConfigT Config (ControllerT TIO)))

{-@ ignore main @-}
main :: IO ()
main = runSqlite ":memory:" $ do
  cfg <- setup
  liftIO . runFrankieServer "dev" $ do
    mode "dev" $ do
      host "localhost"
      port 3000
      initWith $ configure cfg . reading backend . unTag

    dispatch $ do
      get "/" (undefined :: Controller ()) --home
      fallback $ respond notFound

{-@ home :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
home :: Controller ()
home = do
  loggedInUser <- requireAuthUser
  loggedInUserId <- project userIdField loggedInUser
  loggedInUserName <- project userNameField loggedInUser
  shares <- selectList (shareToField ==. loggedInUserId)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers)
  sharedTasks <- projectList todoItemTaskField sharedTodoItems
  page <- renderTemplate Overview
    { overviewUsername = loggedInUserName
    , overviewSharedTasks = sharedTasks
    }

  respondTagged . okHtml . ByteString.fromStrict . Text.encodeUtf8 $ page

{-@ updateSsn :: TaggedT<{\_ -> True}, {\_ -> True}> _ _ @-}
updateSsn :: Controller ()
updateSsn = do
  loggedInUser <- requireAuthUser
  loggedInUserId <- project userIdField loggedInUser
  update loggedInUserId up

{-@ measure newSsn :: Text @-}
{-@ assume newSsn :: {v:_ | v == newSsn} @-}
newSsn :: Text
newSsn = "123456789"

{-@ up :: Update<{\_ -> True}, {\v -> userName (entityVal v) == newSsn }> User @-}
up :: Update User
up = userNameField =. newSsn
