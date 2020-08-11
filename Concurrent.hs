{-# LANGUAGE FlexibleContexts #-}
module Binah.Concurrent
  ( forkTIO
  , ThreadId
  )
where

import           Control.Concurrent

import           Binah.Infrastructure

forkTIO :: MonadTIO m => TIO () -> m ThreadId
forkTIO = liftTIO . TIO . forkIO . runTIO