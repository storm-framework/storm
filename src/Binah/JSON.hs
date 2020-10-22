{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Binah.JSON
  ( respondJSON
  , respondFile
  , jsonResponse
  , emptyResponse
  , respondError
  , errorResponse
  , notFoundJSON
  , decodeBody
  , decodeFiles
  , FileInfo (..)
  )
  where

import           Data.Aeson

import           Binah.Core
import           Binah.Infrastructure
import           Binah.Frankie
import           Binah.Filters
import           Network.Wai.Parse
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString      as BS


{-@ respondJSON :: Status -> a -> TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
respondJSON :: (ToJSON a, MonadController w m) => Status -> a -> TaggedT user m b
respondJSON status a = respondTagged (jsonResponse status a)

{-@ respondError :: Status -> Maybe String -> TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
respondError :: (MonadController w m) => Status -> Maybe String -> TaggedT user m a
respondError status error = respondTagged (errorResponse status error)

{-@ respondFile :: Status -> FileType -> Blob -> TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
respondFile :: (MonadController w m) => Status -> FileType -> Blob -> TaggedT user m a
respondFile status typ blob = respondTagged (blobResponse status typ blob)

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

blobResponse :: Status -> FileType -> LBS.ByteString -> Response
blobResponse status typ blob = Response status [(hContentType, typ)] blob

type FileType = BS.ByteString
type Blob     = LBS.ByteString

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

{-@ decodeFiles :: TaggedT<{\_ -> True}, {\v -> v == currentUser 0}> _ _ _ @-}
decodeFiles :: (MonadTIO m, MonadController TIO m) => TaggedT user m ([Param], [File LBS.ByteString]) 
decodeFiles = do
  req <- requestT
  liftTIO   $ TIO $ parseRequestBodyEx opts lbsBackEnd (waiRequest req)
  where 
    opts    = setMaxRequestFileSize maxSize defaultParseRequestBodyOptions
    maxSize = 1024 * 1024 -- 1Mb




