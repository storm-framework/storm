module Binah.Crypto
  ( encryptPassTIO'
  , module Crypto.Scrypt
  )
where

import           Crypto.Scrypt

import           Binah.Core
import           Binah.Infrastructure


encryptPassTIO' :: MonadTIO m => Pass -> m EncryptedPass
encryptPassTIO' pass = liftTIO (TIO (encryptPassIO' pass))
