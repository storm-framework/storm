{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
module Frankie (reading, assertCurrentUser, respondTagged, module LIO.HTTP.Server.Frankie) where

import Control.Monad.Reader (MonadReader(..), ReaderT(..), withReaderT)
import Data.Typeable (Typeable)
import Control.Monad.Trans (MonadTrans(..))
import Control.Exception (try)
import Data.Text (Text)
import qualified Database.Persist as Persist
import qualified Database.Persist.Sqlite as Persist
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Wai
import qualified Data.Text as Text

import Prelude hiding (log)

import LIO.HTTP.Server.Frankie

import Core
import Model
import Infrastructure
import Filters
import Actions

reading :: Monad m => m r -> ReaderT r m a -> m a
reading r m = r >>= runReaderT m

{-@ measure currentUser :: Entity User @-}

{-@ ignore assertCurrentUser @-}
{-@ assume assertCurrentUser :: u:_ -> {v:TaggedT<{\_ -> True}, {\_ -> False}> _ _ | u == currentUser} @-}
assertCurrentUser :: Monad m => Entity User -> TaggedT m ()
assertCurrentUser _ = return ()

-- TODO: Fill this out
{-
instance MonadController s w m => MonadController s w (TaggedT m) where
  respond :: Response -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> m a
@-}
instance MonadController s w m => MonadController s w (TaggedT m) where
  request = lift request
  respond = respondTagged
  getAppState = lift getAppState
  putAppState = lift . putAppState
  log ll str = lift $ log ll str
  liftWeb = lift . liftWeb

{-@ assume respondTagged :: _ -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> _ _ @-}
respondTagged :: MonadController s w m => Response -> TaggedT m a
respondTagged = lift . respond

instance MonadController s w m => MonadController s w (ReaderT r m) where
  request = lift request
  respond = lift . respond
  getAppState = lift getAppState
  putAppState = lift . putAppState
  log ll str = lift $ log ll str
  liftWeb = lift . liftWeb

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

instance MonadTIO m => MonadTIO (Controller s m) where
  liftTIO = lift . liftTIO

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
