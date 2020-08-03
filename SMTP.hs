{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Binah.SMTP
  ( 
    -- * Parameters needed to send mail
      SMTPConfig (..)
    , Mail
    , Address

    -- * Reading configuration parameters from ENV
    , readSMTPConfig

    -- * Constructing Mail
    , mkPublicAddress

    -- * Sending mail 
    , sendPlainTextMail
    
  ) 
  where

import Data.Maybe (fromMaybe)
import System.Environment (lookupEnv)

import qualified Network.Mail.SMTP as SMTP
import qualified Network.Mail.Mime as Mime
import qualified Network.Socket
import qualified Data.Text         as T
import qualified Data.Text.Lazy    as LT

import           Binah.Infrastructure
import           Binah.Core
import           Binah.Actions
import           Model
import           Control.Exception              ( try
                                                , SomeException(..)
                                                )

-------------------------------------------------------------------------------
-- | Information needed to send an email 
-------------------------------------------------------------------------------
data SMTPConfig = SMTPConfig
  { smtpHost :: Network.Socket.HostName
  , smtpPort :: Network.Socket.PortNumber
  , smtpUser :: SMTP.UserName
  , smtpPass :: SMTP.Password
  }

-------------------------------------------------------------------------------
-- | An `example` of how to obtain an SMTPConfig and then send mail
-------------------------------------------------------------------------------
example :: MonadTIO m => TaggedT m ()
example = liftTIO $ TIO $ do
  config <- readSMTPConfig "VOLTRON"
  sendMail config exampleMail

exampleMail :: Mail
exampleMail = mkMail from to subject body
  where
    from    = mkPublicAddress  "rjhala@eng.ucsd.edu"
    to      = mkPublicAddress "rjhala@eng.ucsd.edu"
    subject = "email subject"
    body    = "This is the body"


-------------------------------------------------------------------------------
-- | `readSMTPConfig appPrefix` returns the `SMTPConfig`; for example,
--   `readSMTPConfig "VOLTRON"` will read the environment variables 
--   `VOLTRON_SMTP_HOST`, `VOLTRON_SMTP_PORT`, `VOLTRON_SMTP_USER` 
--    and `VOLTRON_SMTP_PASS` to create the `SMTPConfig` that can 
--    then be used to send mail.
-------------------------------------------------------------------------------
readSMTPConfig :: String -> IO SMTPConfig
readSMTPConfig appPrefix = do
    host <- fromMaybe "localhost" <$> lookupEnv hostVar 
    port <- fromMaybe "425"       <$> lookupEnv portVar
    user <- fromMaybe ""          <$> lookupEnv userVar
    pass <- fromMaybe ""          <$> lookupEnv passVar
    return $ SMTPConfig host (read port) user pass
    where 
      hostVar = appPrefix <> "_" <> "SMTP_HOST"
      portVar = appPrefix <> "_" <> "SMTP_PORT"
      userVar = appPrefix <> "_" <> "SMTP_USER"
      passVar = appPrefix <> "_" <> "SMTP_PASS"

-- TODO: LIQUID TYPES

newtype Mail = Mail Mime.Mail

{-@ data Address<out :: Entity User -> Bool> = Address _ @-}
{-@ data variance Address covariant @-}
data Address = Address { unAddress :: String }

{-@ assume mkPublicAddress :: String -> Address<{\_ -> True}> @-}
mkPublicAddress :: String -> Address
mkPublicAddress = Address


-- | Sending plain text email --------------------------------------------------------------

-- | Constructing Mail and Address ---------------------------------------------------------

mkMail :: Address -> Address -> T.Text -> LT.Text -> Mail
mkMail from to subject body =
  Mail $ Mime.simpleMail' (mimeAddress from) (mimeAddress to) subject body

mimeAddress :: Address -> Mime.Address
mimeAddress (Address a) = Mime.Address Nothing (T.pack a)

renderSendMail :: MonadTIO m => Mail -> TaggedT m ()
renderSendMail (Mail mail) = liftTIO $ TIO $ SMTP.renderSendMail mail


newtype SMTPError = SendError String deriving Show


-- FIXME: The source label shouldn't be True because the exception could contain part of the email's
-- content.
{-@
assume sendPlainTextMail :: forall <out :: Entity User -> Bool>.
     SMTPConfig
  -> Address<out>
  -> Address
  -> String
  -> _
  -> SMTPConnection
  -> TaggedT<{\_ -> True}, out> m (Either SMTPError ())
@-}
sendPlainTextMail
  :: MonadTIO m
  => SMTPConfig
  -> Address
  -> Address
  -> T.Text 
  -> LT.Text
  -> TaggedT m (Either SMTPError ())
sendPlainTextMail cfg to from subject body = liftTIO $ TIO $ do
  res <- try $ sendMail cfg $ mkMail from to subject body
  case res of
    Left  (SomeException e) -> return (Left (SendError (show e)))
    Right _                 -> return (Right ())

-------------------------------------------------------------------------------
sendMail :: SMTPConfig -> Mail -> IO ()
-------------------------------------------------------------------------------
sendMail (SMTPConfig {..}) (Mail mail) = 
  SMTP.sendMailWithLoginSTARTTLS smtpHost smtpUser smtpPass mail

-- authenticate LOGIN user pass conn ==> 
authenticate :: MonadTIO m => SMTP.AuthType -> String -> String -> SMTP.SMTPConnection -> m Bool
authenticate auth user pass conn = liftTIO $ TIO $ do 
  (code, _) <- SMTP.sendCommand conn (SMTP.AUTH auth user pass) -- authenticate auth user pass conn
  return (code == 235)

-- http://hackage.haskell.org/package/HaskellNet-0.5.1/docs/src/Network-HaskellNet-SMTP.html#authenticate