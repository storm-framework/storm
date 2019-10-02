{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Frankie (MonadController(..), AuthenticatedT(..), MonadAuthenticated(..), HasSqlBackend(..), reading, respondTagged, assertCurrentUser, getLoggedInUserTagged, module LIO.HTTP.Server.Frankie) where

import Control.Monad.Reader (MonadReader(..), ReaderT(..), withReaderT)
import Data.Typeable (Typeable)
import Control.Monad.Trans (MonadTrans(..))
import Control.Exception (try)
import Data.Text (Text)
import Control.Monad ((>=>))
import qualified Database.Persist as Persist
import qualified Database.Persist.Sqlite as Persist
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Wai
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Base64 as Base64
import Data.Either.Combinators (rightToMaybe)
import qualified Data.Text.Encoding as Text
import Data.Maybe (fromJust)

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

instance (Typeable s, Typeable m, Typeable a, RequestHandler (m a) s w) => RequestHandler (TaggedT m a) s w where
  handlerToController args = handlerToController args . unTag
  reqHandlerArgTy = reqHandlerArgTy . unTag

data AuthenticatedT m a = AuthenticatedT { runAuthenticatedT :: Entity User -> m a }

instance Functor m => Functor (AuthenticatedT m) where
  fmap f x = AuthenticatedT (fmap f . runAuthenticatedT x)

instance Applicative m => Applicative (AuthenticatedT m) where
  pure x = AuthenticatedT $ const (pure x)
  f <*> x = AuthenticatedT $ \user -> runAuthenticatedT f user <*> runAuthenticatedT x user

instance Monad m => Monad (AuthenticatedT m) where
  x >>= f = AuthenticatedT $ \user -> runAuthenticatedT x user >>= (`runAuthenticatedT` user) . f

class Monad m => MonadAuthenticated m where
  getLoggedInUser :: m (Entity User)

instance Monad m => MonadAuthenticated (AuthenticatedT m) where
  getLoggedInUser = AuthenticatedT pure

{-
instance MonadAuthenticated m => MonadAuthenticated (TaggedT m) where
  getLoggedInUser :: TaggedT<{\_ -> True}, {\_ -> False}> m {u:(Entity User) | u == currentUser}
@-}
instance MonadAuthenticated m => MonadAuthenticated (TaggedT m) where
  getLoggedInUser = getLoggedInUserTagged

{-@ assume getLoggedInUserTagged :: TaggedT<{\_ -> True}, {\_ -> False}> _ {u:(Entity User) | u == currentUser && entityKey u == entityKey currentUser && entityVal u == entityVal currentUser} @-}
getLoggedInUserTagged :: MonadAuthenticated m => TaggedT m (Entity User)
getLoggedInUserTagged = lift getLoggedInUser

instance MonadAuthenticated m => MonadAuthenticated (ReaderT r m) where
  getLoggedInUser = lift getLoggedInUser

instance MonadTrans AuthenticatedT where
  lift x = AuthenticatedT $ const x

instance MonadTIO m => MonadTIO (AuthenticatedT m) where
  liftTIO = lift . liftTIO

instance MonadController s w m => MonadController s w (AuthenticatedT m) where
  request = lift request
  respond = lift . respond
  getAppState = lift getAppState
  putAppState = lift . putAppState
  log ll str = lift $ log ll str
  liftWeb = lift . liftWeb

class HasSqlBackend config where
  getSqlBackend :: config -> Persist.SqlBackend

backend :: (MonadController config w m, HasSqlBackend config) => m Persist.SqlBackend
backend = getSqlBackend <$> getAppState

instance forall m w a config. (MonadTIO w, Typeable m, Typeable a, RequestHandler (m a) config w, MonadTIO m, WebMonad w, HasSqlBackend config) => RequestHandler (AuthenticatedT m a) config w where
  handlerToController = handlerToControllerAuthenticatedT
  reqHandlerArgTy _ = reqHandlerArgTy (undefined :: m a) -- TODO: Fix this bad thing

{-@ ignore handlerToControllerAuthenticatedT @-}
handlerToControllerAuthenticatedT :: (MonadTIO w, Typeable m, Typeable a, RequestHandler (m a) config w, MonadTIO m, WebMonad w, HasSqlBackend config) => [PathSegment] -> AuthenticatedT m a -> Controller config w ()
handlerToControllerAuthenticatedT args handler = do
       authHeader <- requestHeader hAuthorization
       case authHeader >>= parseBasicAuthHeader of
         Just (username, _) -> do
           back <- backend
           user <- (`runReaderT` back) $ unTag $ selectFirst (userNameField ==. username ?: nilFL)
           handlerToController args (runAuthenticatedT handler (fromJust user))
         Nothing -> respond $ requireBasicAuth "this website"


parseBasicAuthHeader :: ByteString -> Maybe (Text, Text)
parseBasicAuthHeader =
  ByteString.stripPrefix "Basic " >=>
  rightToMaybe . Base64.decode >=>
  rightToMaybe . Text.decodeUtf8' >=>
  splitAtChar ':'
  where
    splitAtChar :: Char -> Text -> Maybe (Text, Text)
    splitAtChar c text =
      let (before, after) = Text.break (== c) text in do
      (_, after') <- Text.uncons after
      return (before, after')

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
