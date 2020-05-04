{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Binah.Frankie (MonadController(..), HasSqlBackend(..), reading, backend, respondTagged, requireAuthUser, module Frankie) where

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

import Frankie
import Frankie.Config
import Frankie.Auth
import qualified Frankie.Auth

import Binah.Core
import Binah.Infrastructure


reading :: Monad m => m r -> ReaderT r m a -> m a
reading r m = r >>= runReaderT m

{-@ measure currentUser :: user @-}

-- TODO: Fill this out
{-
instance MonadController s w m => MonadController s w (TaggedT user m) where
  respond :: Response -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> user m a
@-}
instance MonadController w m => MonadController w (TaggedT user m) where
  request = lift request
  respond = respondTagged
  liftWeb x = lift (liftWeb x)

{-@ assume respondTagged :: _ -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> _ _ _ @-}
respondTagged :: MonadController w m => Response -> TaggedT user m a
respondTagged x = lift (respond x)

{-@ assume requireAuthUser :: m {u:user | u == currentUser} @-}
requireAuthUser :: MonadAuth user m => m user
requireAuthUser = requireAuth

instance MonadConfig config m => MonadConfig config (TaggedT user m) where
  getConfig = lift getConfig

instance MonadController w m => MonadController w (ReaderT r m) where
  request = lift request
  respond x = lift (respond x)
  liftWeb x = lift (liftWeb x)

instance MonadConfig config m => MonadConfig config (ReaderT r m) where
  getConfig = lift getConfig

instance MonadTIO m => MonadTIO (ConfigT config m) where
  liftTIO x = lift (liftTIO x)

class HasSqlBackend config where
  getSqlBackend :: config -> Persist.SqlBackend

backend :: (MonadConfig config m, HasSqlBackend config) => m Persist.SqlBackend
backend = getSqlBackend <$> getConfig

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
                   Wai.setServerName "frankie" $ Wai.defaultSettings
    in Wai.runSettings settings $ toWaiApplication app

instance MonadTIO m => MonadTIO (ControllerT m) where
  liftTIO x = lift (liftTIO x)

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
