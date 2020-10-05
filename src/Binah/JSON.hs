{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Binah.JSON
  ( respondJSON
  , jsonResponse
  , emptyResponse
  , respondError
  , errorResponse
  , notFoundJSON
  , decodeBody
  )
  where

import           Data.Aeson

import           Binah.Core
import           Binah.Infrastructure
import           Binah.Frankie
import           Binah.Filters

{-@ respondJSON :: Status -> a -> TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
respondJSON :: (ToJSON a, MonadController w m) => Status -> a -> TaggedT user m b
respondJSON status a = respondTagged (jsonResponse status a)

{-@ respondError :: Status -> Maybe String -> TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
respondError :: (MonadController w m) => Status -> Maybe String -> TaggedT user m a
respondError status error = respondTagged (errorResponse status error)

--------------------------------------------------------------------------------
-- | Responses
--------------------------------------------------------------------------------

defaultHeaders :: ResponseHeaders
defaultHeaders = [(hContentType, "application/json")]

jsonResponse :: ToJSON a => Status -> a -> Response
jsonResponse status a = Response status defaultHeaders (encode a)

emptyResponse :: Status -> Response
emptyResponse status = Response status defaultHeaders ""

errorResponse :: Status -> Maybe String -> Response
errorResponse status error = Response status defaultHeaders (encodeError error)
 where
  encodeError Nothing  = encode $ object []
  encodeError (Just e) = encode $ object ["error" .= e]

notFoundJSON :: Response
notFoundJSON = errorResponse status404 Nothing

--------------------------------------------------------------------------------
-- | Decoding
--------------------------------------------------------------------------------

{-@ decodeBody :: TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
decodeBody :: (FromJSON a, MonadTIO m, MonadController TIO m) => TaggedT user m a
decodeBody = do
  req  <- requestT
  body <- liftTIO $ reqBody req
  case eitherDecode body of
    Left  s -> respondError status400 (Just s)
    Right a -> return a
