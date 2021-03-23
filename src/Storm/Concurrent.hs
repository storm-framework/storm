{-# LANGUAGE FlexibleContexts #-}
module Storm.Concurrent
  ( forkTIO
  , ThreadId
  )
where

import           Control.Concurrent

import           Storm.Core
import           Storm.Infrastructure

forkTIO :: MonadTIO m => TIO () -> m ThreadId
forkTIO act = liftTIO (TIO (forkIO (runTIO act)))