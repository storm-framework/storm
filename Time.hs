module Binah.Time where

import           Control.Monad.Time             ( MonadTime(..) )

import           Binah.Core
import           Binah.Infrastructure

instance MonadTime TIO where
  currentTime = TIO currentTime