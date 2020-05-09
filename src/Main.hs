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
import Database.Persist (PersistStoreWrite, PersistRecordBackend)

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
import Binah.Insert
import Model

-- * Client code

data Config = Config
  { configBackend :: !SqlBackend
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


{-@ ignore setup @-}
setup :: MonadIO m => ReaderT SqlBackend m Config
setup = do
  templateCache <- liftIO $ newMVar mempty

  runMigration migrateAll

  backend <- ask

  liftIO . runTIO . flip runReaderT backend . unTag $ initDB

  return $  Config
    { configBackend = backend
    , configTemplateCache = templateCache
    , configAuthMethod = httpAuthDb
    }

{-@ initDB :: TaggedT<{\_ -> True}, {\_-> True}> _ _ @-}
initDB :: TaggedT (ReaderT SqlBackend TIO) ()
initDB = do
  aliceId <- insert $ mkUser "Alice" "123456789"
  bobId   <- insert $ mkUser "Bob" "987654321"

  insert $ mkTodoItem bobId "Get groceries"
  insert $ mkTodoItem bobId "Submit paper"
  insert $ mkTodoItem aliceId "Research"

  insert $ mkShare bobId aliceId

  return ()

{-@ ignore httpAuthDb @-}
httpAuthDb :: AuthMethod (Entity User) Controller
httpAuthDb = httpBasicAuth $ \username _password -> selectFirst (userName' ==. username)

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
home :: Controller (Entity User)
home = do
  loggedInUser <- requireAuthUser
  loggedInUserId <- project userId' loggedInUser
  loggedInUserName <- project userName' loggedInUser
  shares <- selectList (shareTo' ==. loggedInUserId)
  sharedFromUsers <- projectList shareFrom' shares
  sharedTodoItems <- selectList (todoItemOwner' <-. sharedFromUsers)
  sharedTasks <- projectList todoItemTask' sharedTodoItems
  page <- renderTemplate Overview
    { overviewUsername = loggedInUserName
    , overviewSharedTasks = sharedTasks
    }

  respondTagged . okHtml . ByteString.fromStrict . Text.encodeUtf8 $ page
