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
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Database.Persist.Sql (SqlBackend, Migration)
import Database.Persist (PersistStoreWrite, PersistRecordBackend)
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

-- TODO: This code should be in a library somewhere

runSqlite :: Text -> ReaderT SqlBackend TIO a -> TIO a
runSqlite connStr action = TIO . Persist.runSqlite connStr $ do
  backend <- ask
  liftIO . runTIO . (`runReaderT` backend) $ action

runMigration :: (MonadTIO m, MonadReader SqlBackend m) => Migration -> m ()
runMigration migration = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Persist.runMigration migration

insert :: (PersistStoreWrite backend, PersistRecordBackend record backend, MonadTIO m, MonadReader backend m) => record -> m (Key record)
insert record = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Persist.insert record

-- -- TODO: Remove the Sqlite stuff from main once mapTaggedT gets worked out
-- {-@ ignore main @-}
-- main :: IO ()
-- main = runTIO . unTag . mapTaggedT (runSqlite ":memory:") $ taggedMain

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
  user <- fromJust <$> selectFirst (userIdField ==. userId ?: nilFL)
  shares <- selectList (shareToField ==. userId ?: nilFL)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: nilFL)
  tasks <- projectList todoItemTaskField sharedTodoItems
  printTo user $ show tasks

main :: IO ()
main = runFrankieServer "dev" $ do
  mode "dev" $ do
    host "localhost"
    port 3000
    appState ()

  dispatch $ do
    get "/" home
    fallback $ respond notFound

home :: TaggedT (Controller () TIO) ()
home = lift $ respond $ okHtml "Hello, world!"

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
          req = let pI0 = Wai.pathInfo wReq
                    pI1 = if (not . null $ pI0) && (last pI0 == Text.empty)
                            then init pI0
                            else pI0
                in RequestTIO $ wReq { Wai.pathInfo = pI1 }
          toWaiResponse :: Response -> Wai.Response
          toWaiResponse (Response status headers body) = Wai.responseLBS status headers body
