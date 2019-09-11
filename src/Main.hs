{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Main where

import Data.Maybe (fromJust)
import Data.Text (Text)
import Control.Exception (try)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), withReaderT)
import Database.Persist.Sqlite (SqlBackend, Migration, runMigration, runSqlite)
import Database.Persist (PersistStoreWrite, PersistRecordBackend, insert)

import qualified Data.ByteString.Lazy as ByteString
import qualified Data.Text.Encoding as Text
import qualified Text.Mustache as Mustache
import Text.Mustache ((~>))
import Text.Mustache.Types as Mustache

import Core
import Model
import Infrastructure
import Filters
import Actions
import Frankie

-- * Client code

data Config = Config
  { configBackend :: !SqlBackend
  , configAliceId :: !UserId
  , configBobId :: !UserId
  , configOverviewTemplate :: !Mustache.Template
  }

getBackend :: MonadController Config w m => m SqlBackend
getBackend = configBackend <$> getAppState

getAliceId :: MonadController Config w m => m UserId
getAliceId = configAliceId <$> getAppState

getBobId :: MonadController Config w m => m UserId
getBobId = configBobId <$> getAppState

getOverviewTemplate :: MonadController Config w m => m Mustache.Template
getOverviewTemplate = configOverviewTemplate <$> getAppState

setup :: MonadIO m => ReaderT SqlBackend m Config
setup = do
  template <- liftIO $ unwrap <$> Mustache.automaticCompile ["templates"] "overview.html.mustache"

  runMigration migrateAll

  aId <- insert $ User "Alice" "123456789"
  bId <- insert $ User "Bob" "987654321"

  insert $ TodoItem bId "Get groceries"
  insert $ TodoItem bId "Submit paper"
  insert $ TodoItem aId "Research"

  insert $ Share bId aId

  back <- ask
  return $ Config back aId bId template

{-@ ignore unwrap @-}
unwrap :: Show a => Either a b -> b
unwrap (Right x) = x
unwrap (Left e) = error ("Unexpected Left: " ++ show e)

{-@ ignore main @-}
main :: IO ()
main = runSqlite ":memory:" $ do
  cfg <- setup
  liftIO . runFrankieServer "dev" $ do
    mode "dev" $ do
      host "localhost"
      port 3000
      appState cfg

    dispatch $ do
      get "/" home
      fallback $ respond notFound

{-@ home :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
home :: TaggedT (Controller Config TIO) ()
home = mapTaggedT (reading getBackend) $ do
  aliceId <- getAliceId
  template <- getOverviewTemplate

  alice <- fromJust <$> selectFirst (userIdField ==. aliceId ?: nilFL)
  assertCurrentUser alice

  aliceUserName <- project userNameField alice

  shares <- selectList (shareToField ==. aliceId ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  sharedTasks <- projectList todoItemTaskField sharedTodoItems

  respondTagged . okHtml . ByteString.fromStrict . Text.encodeUtf8 $ Mustache.substitute template (templateArgs aliceUserName sharedTasks)

  where
    templateArgs :: String -> [String] -> Mustache.Value
    templateArgs u s = Mustache.object
      [ "username" ~> u
      , "sharedTasks" ~> map (\task -> Mustache.object ["text" ~> task]) s
      ]
