module Binah.SMTP
  ( SMTPConnection
  , UserName
  , Password
  , Address
  , Mail
  , connectSMTPS'
  , login
  , publicAddress
  , simpleMail'
  , renderAndSend
  , sendMailWithLoginSTARTTLS
  )
where

import           Control.Exception ( try
                                   , SomeException(..)
                                   )
import           Data.ByteString   (ByteString)
import qualified Data.Text         as T
import qualified Data.Text.Lazy    as LT
import qualified Network.Mail.Mime as Mime
import qualified Network.Mail.SMTP as SMTP
import           Network.Mail.SMTP ( SMTPConnection
                                   , UserName
                                   , Password
                                   , ReplyCode
                                   )
import qualified Network.Socket

import           Binah.Core
import           Binah.Infrastructure

newtype SMTPError = SendError String deriving Show

{-@ data Mail user <sink :: user -> Bool> = Mail _ @-}
{-@ data variance Mail covariant @-}
data Mail user = Mail Mime.Mail

{-@ data Address user <sink :: user -> Bool> = Address _ @-}
{-@ data variance Address covariant @-}
data Address user = Address Mime.Address


-- | Create mails and addresses

{-@ assume publicAddress :: _ -> Address<{\_ -> True}> user @-}
publicAddress :: T.Text -> Address user
publicAddress addr = Address (Mime.Address Nothing addr)

{-@ assume simpleMail' :: forall < p :: user -> Bool, q :: user -> Bool>.
      Address<p> user -> Address<q> user -> _ -> _ -> Mail<q> user
@-}
simpleMail' :: Address user -> Address user -> T.Text -> LT.Text -> Mail user
simpleMail' (Address to) (Address from) subject body =
  Mail $ Mime.simpleMail' to from subject body

-- | Connection

connectSMTPS'
  :: MonadTIO m
  => Network.Socket.HostName
  -> Network.Socket.PortNumber
  -> m SMTPConnection
connectSMTPS' host port = liftTIO $ TIO $ SMTP.connectSMTPS' host port

login
  :: MonadTIO m
  => SMTPConnection
  -> UserName
  -> Password
  -> m (ReplyCode, ByteString)
login conn user pass = liftTIO $ TIO $ SMTP.login conn user pass


-- | Send mail

-- FIXME: The source label shouldn't be True because the exception could contain
-- part of the email's content.
{-@ assume renderAndSend :: forall <sink :: user -> Bool>.
      SMTPConnection -> Mail<sink> user -> TaggedT<{\_ -> True}, sink> user m (Either SMTPError ())
@-}
renderAndSend
  :: MonadTIO m
  => SMTPConnection
  -> Mail user
  -> TaggedT user m (Either SMTPError ())
renderAndSend conn (Mail mail) = TaggedT $ liftTIO $ TIO $ do
  res <- try $ SMTP.renderAndSend conn mail
  case res of
    Left (SomeException e) -> return (Left (SendError (show e)))
    Right _                -> return (Right ())


sendMailWithLoginSTARTTLS
  :: MonadTIO m
  => Network.Socket.HostName
  -> UserName
  -> Password
  -> Mail user
  -> TaggedT user m (Either SMTPError ())
sendMailWithLoginSTARTTLS host user pass (Mail mail) = TaggedT $ liftTIO $ TIO $ do
  res <- try $ SMTP.sendMailWithLoginSTARTTLS host user pass mail
  case res of
    Left (SomeException e) -> return (Left (SendError (show e)))
    Right _                -> return (Right ())