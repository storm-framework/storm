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
import Text.Mustache ((~>))
import Text.Mustache.Types as Mustache
import Control.Concurrent.MVar
import qualified Data.HashMap.Strict as HashMap

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
  , configTemplateCache :: !(MVar Mustache.TemplateCache)
  }

class ToMustache d => TemplateData d where
  templateFile :: FilePath

{-@ ignore getOrLoadTemplate @-}
getOrLoadTemplate :: (MonadController Config w m, MonadTIO m) => [FilePath] -> FilePath -> m Mustache.Template
getOrLoadTemplate searchDirs file = do
  cacheMVar <- configTemplateCache <$> getAppState
  oldCache <- liftTIO $ TIO (readMVar cacheMVar)
  case HashMap.lookup file oldCache of
    Just template -> pure template
    Nothing -> do
      liftTIO $ TIO $ Mustache.compileTemplateWithCache searchDirs oldCache file >>= \case
        Right template ->
          let updatedCache = HashMap.insert (name template) template (partials template) in do
            modifyMVar_ cacheMVar (\currentCache -> evaluate $ currentCache <> updatedCache)
            pure template
        Left err -> error $ "Error parsing template " ++ file ++ ": " ++ show err

{-@ assume renderTemplate :: _ -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
{-@ ignore renderTemplate @-}
renderTemplate :: forall d w m. (MonadController Config w m, MonadTIO m, TemplateData d) => d -> TaggedT m Text
renderTemplate templateData = do
  template <- getOrLoadTemplate searchDirs file
  pure $ Mustache.substitute template templateData
  where
    file = templateFile @d
    searchDirs = ["templates"]

data Overview = Overview
  { overviewUsername :: Text
  , overviewSharedTasks :: [Text]
  }

instance TemplateData Overview where
  templateFile = "overview.html.mustache"

instance ToMustache Overview where
  toMustache (Overview username tasks) = object
    [ "username" ~> toMustache username
    , "sharedTasks" ~> (toMustache $ map (\task -> object ["text" ~> task]) tasks)
    ]


getBackend :: MonadController Config w m => m SqlBackend
getBackend = configBackend <$> getAppState

getAliceId :: MonadController Config w m => m UserId
getAliceId = configAliceId <$> getAppState

getBobId :: MonadController Config w m => m UserId
getBobId = configBobId <$> getAppState

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
    }

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

  alice <- fromJust <$> selectFirst (userIdField ==. aliceId ?: nilFL)
  assertCurrentUser alice

  aliceUsername <- project userNameField alice

  shares <- selectList (shareToField ==. aliceId ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  sharedTasks <- projectList todoItemTaskField sharedTodoItems

  page <- renderTemplate Overview
    { overviewUsername = aliceUsername
    , overviewSharedTasks = sharedTasks
    }

  respondTagged . okHtml . ByteString.fromStrict . Text.encodeUtf8 $ page

-- {-@ displayTasks @-}
-- displayTasks :: UserId -> TaggedT (Controller Config TIO) ()
-- displayTasks userId = mapTaggedT (reading getBackend) $ do
--   user <- fromJust <$> selectFirst (userIdField ==. userId ?: nilFL)
--   assertCurrentUser user

--   todoItems <- selectList (todoItemOwnerField ==. userId)
--   tasks <- projectList todoItemTaskField todoItems

--   respondTagged . okHtml . ByteString.fromStrict . Text.encodeUtf8 <$> renderTemplate $ Overview
--     { overviewUsername =
--     ,
--     }
