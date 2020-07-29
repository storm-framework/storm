{-# LANGUAGE FlexibleContexts #-}
module Binah.Concurrent
  ( forkTIO
  , ThreadId
  )
where

import           Database.Persist.Sqlite        ( SqlBackend )

import           Control.Concurrent

import           Binah.Core
import           Binah.Infrastructure
import           Model

forkTIO :: MonadTIO m => TIO () -> m ThreadId
forkTIO = liftTIO . TIO . forkIO . runTIO
