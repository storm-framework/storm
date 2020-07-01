{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Binah.Frankie
  ( MonadController(..)
  , respondTagged
  , requireAuthUser
  , parseForm
  , initWithT
  , getConfigT
  , requestT
  , module Frankie
  )
where

import           Control.Monad.Reader           ( MonadReader(..)
                                                , ReaderT(..)
                                                )
import           Data.Typeable                  ( Typeable )
import           Control.Monad.Trans            ( MonadTrans(..) )
import           Control.Exception              ( try )
import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as T
import qualified Database.Persist              as Persist
import qualified Database.Persist.Sqlite       as Persist
import qualified Network.Wai                   as Wai
import qualified Network.Wai.Handler.Warp      as Wai
import qualified Network.Wai.Parse             as Wai
import           Data.Bifunctor                 ( bimap )

import           Prelude                 hiding ( log )

import           Frankie
import           Frankie.Config
import           Frankie.Auth
import qualified Frankie.Auth

import           Binah.Core
import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Actions

import           Model
import           Text.Read                      ( readMaybe )

-- TODO: Fill this out
{-
instance MonadController s w m => MonadController s w (TaggedT m) where
  respond :: Response -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> m a
@-}
instance MonadController w m => MonadController w (TaggedT m) where
  request = lift request
  respond = respondTagged
  liftWeb x = lift (liftWeb x)

{-@ requestT :: TaggedT<{\_ -> True}, {\_ -> False}> m (Request w) @-}
requestT :: MonadController w m => TaggedT m (Request w)
requestT = liftT request

{-@ assume respondTagged :: _ -> TaggedT<{\_ -> True}, {\u -> u == currentUser}> _ _ @-}
respondTagged :: MonadController w m => Response -> TaggedT m a
respondTagged x = lift (respond x)

{-@ assume requireAuthUser :: m {u:(Entity User) | u == currentUser} @-}
requireAuthUser :: MonadAuth (Entity User) m => m (Entity User)
requireAuthUser = requireAuth

{-@ getConfigT :: TaggedT<{\_ -> True}, {\_ -> False}> m config @-}
getConfigT :: MonadConfig config m => TaggedT m config
getConfigT = liftT getConfig

-- TODO: Check why this type is not being exported
{-
instance MonadConfig config m => MonadConfig config (TaggedT m) where
  getConfig :: TaggedT<{\_ -> True}, {\_ -> False}> m config
@-}
instance MonadConfig config m => MonadConfig config (TaggedT m) where
  getConfig = getConfigT

instance MonadController w m => MonadController w (ReaderT r m) where
  request = lift request
  respond x = lift (respond x)
  liftWeb x = lift (liftWeb x)

instance MonadConfig config m => MonadConfig config (ReaderT r m) where
  getConfig = lift getConfig

instance MonadTIO m => MonadTIO (ConfigT config m) where
  liftTIO x = lift (liftTIO x)

instance WebMonad TIO where
  data Request TIO = RequestTIO { unRequestTIO :: Wai.Request }
  reqMethod      = Wai.requestMethod . unRequestTIO
  reqHttpVersion = Wai.httpVersion . unRequestTIO
  reqPathInfo    = Wai.pathInfo . unRequestTIO
  reqQueryString = Wai.queryString . unRequestTIO
  reqHeaders     = Wai.requestHeaders . unRequestTIO
  reqBody        = TIO . Wai.strictRequestBody . unRequestTIO
  tryWeb act = do
    er <- (TIO . try . runTIO) act
    case er of
      Left e -> return . Left . toException $ e
      r      -> return r
  server port hostPref app =
    let settings =
            Wai.setHost hostPref
              $ Wai.setPort port
              $ Wai.setServerName "frankie"
              $ Wai.defaultSettings
    in  Wai.runSettings settings $ toWaiApplication app

instance MonadTIO m => MonadTIO (ControllerT m) where
  liftTIO x = lift (liftTIO x)

-- initWithT :: (TaggedT m () -> TaggedT (ControllerT w) ()) -> Frankie.FrankieConfigMode w m ()
initWithT initializeFun = initWith $ unTag . initializeFun

toWaiApplication :: Application TIO -> Wai.Application
toWaiApplication app wReq wRespond = do
  resp <- runTIO $ app req
  wRespond $ toWaiResponse resp
 where
  req :: Request TIO
  req = RequestTIO $ wReq { Wai.pathInfo = trimPath $ Wai.pathInfo wReq }
  toWaiResponse :: Response -> Wai.Response
  toWaiResponse (Response status headers body) = Wai.responseLBS status headers body

{-@ ignore trimPath @-}
trimPath :: [T.Text] -> [T.Text]
trimPath path = if (not . null $ path) && T.null (last path) then init path else path

{-@ ignore parseForm @-}
{-@ parseForm :: TaggedT<{\_ -> True }, {\_ -> False}> _ _ @-}
parseForm :: (MonadController TIO m, MonadTIO m) => TaggedT m [(T.Text, T.Text)]
parseForm = do
  req    <- request
  parsed <- liftTIO $ TIO $ Wai.parseRequestBody Wai.lbsBackEnd $ unRequestTIO req
  return $ map (bimap T.decodeUtf8 T.decodeUtf8) (fst parsed)

instance (Persist.ToBackendKey Persist.SqlBackend record, Typeable record) => Parseable (Key record) where
  parseText = fmap Persist.toSqlKey . readMaybe . T.unpack
