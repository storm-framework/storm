module Storm.Crypto
  ( encryptPassTIO'
  , module Crypto.Scrypt
  )
where

import           Crypto.Scrypt

import           Storm.Core
import           Storm.Infrastructure


encryptPassTIO' :: MonadTIO m => Pass -> m EncryptedPass
encryptPassTIO' pass = liftTIO (TIO (encryptPassIO' pass))
