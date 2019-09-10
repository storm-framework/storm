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
import Data.ByteString.Lazy.Char8 (pack)
import Control.Exception (try)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Database.Persist.Sqlite (SqlBackend, Migration, runMigration, runSqlite)
import Database.Persist (PersistStoreWrite, PersistRecordBackend, insert)
import Data.Typeable (Typeable)
import qualified Database.Persist as Persist
import qualified Database.Persist.Sqlite as Persist
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Wai
import qualified Data.Text as Text

import LIO.HTTP.Server.Frankie

import Core
import Model
import Infrastructure
import Filters
import Actions

-- * Client code

data Config = Config
  { backend :: SqlBackend
  , aliceId :: UserId
  , bobId :: UserId
  }

setup :: MonadIO m => ReaderT SqlBackend m Config
setup = do
  runMigration migrateAll

  aId <- insert $ User "Alice" "123456789"
  bId <- insert $ User "Bob" "987654321"

  insert $ TodoItem bId "Get groceries"
  insert $ TodoItem bId "Submit paper"
  insert $ TodoItem aId "Research"

  insert $ Share bId aId

  back <- ask
  return $ Config back aId bId

{-@ getSharedWith :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
getSharedWith :: (MonadReader SqlBackend m, MonadTIO m) => UserId -> TaggedT m [String]
getSharedWith userId = do
  user <- fromJust <$> selectFirst (userIdField ==. userId ?: nilFL)
  shares <- selectList (shareToField ==. userId ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  projectList todoItemTaskField sharedTodoItems

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

home :: TaggedT (Controller Config TIO) ()
home = do
  aId <- aliceId <$> lift getAppState
  sharedTasks <- mapTaggedT (readingLocal backend) $ getSharedWith aId
  lift . respond . okHtml . pack . show $ sharedTasks

readingLocal :: Monad m => (s -> r) -> ReaderT r m a -> Controller s m a
readingLocal f m = getAppState >>= lift . runReaderT m . f

test :: Monad m => TaggedT (Controller Config m) Config
test = lift getAppState

instance (Typeable s, Typeable m, Typeable a, RequestHandler (Controller s m a) s m) => RequestHandler (TaggedT (Controller s m) a) s m where
  handlerToController args = handlerToController args . unTag
  reqHandlerArgTy = reqHandlerArgTy . unTag

instance WebMonad TIO where
  data Request TIO = RequestTIO { unRequestTIO :: Wai.Request }
  reqMethod      = Wai.requestMethod . unRequestTIO
  reqHttpVersion = Wai.httpVersion . unRequestTIO
  reqPathInfo    = Wai.pathInfo . unRequestTIO
  reqQueryString = Wai.queryString . unRequestTIO
  reqHeaders     = Wai.requestHeaders . unRequestTIO
  reqBody        = TIO . Wai.strictRequestBody . unRequestTIO
  tryWeb act     = do er <- (TIO . try . runTIO) act
                      case er of
                        Left e -> return . Left . toException $ e
                        r -> return r
  server port hostPref app =
    let settings = Wai.setHost hostPref $ Wai.setPort port $
                   Wai.setServerName "lio-http-server" $ Wai.defaultSettings
    in Wai.runSettings settings $ toWaiApplication app

toWaiApplication :: Application TIO -> Wai.Application
toWaiApplication app wReq wRespond = do
  resp <- runTIO $ app req
  wRespond $ toWaiResponse resp
    where req :: Request TIO
          req = RequestTIO $ wReq { Wai.pathInfo = trimPath $ Wai.pathInfo wReq }
          toWaiResponse :: Response -> Wai.Response
          toWaiResponse (Response status headers body) = Wai.responseLBS status headers body

{-@ ignore trimPath @-}
trimPath :: [Text] -> [Text]
trimPath path =
  if (not . null $ path) && Text.null (last path)
  then init path
  else path
