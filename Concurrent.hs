{-# LANGUAGE FlexibleContexts #-}
module Binah.Concurrent
  ( forkTIO
  , ThreadId
  )
where

import           Control.Concurrent

import           Binah.Core
import           Binah.Infrastructure

forkTIO :: MonadTIO m => TIO () -> m ThreadId
forkTIO act = liftTIO (TIO (forkIO (runTIO act)))