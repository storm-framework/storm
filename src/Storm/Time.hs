module Storm.Time where

import           Control.Monad.Time             ( MonadTime(..) )

import           Storm.Core
import           Storm.Infrastructure

instance MonadTime TIO where
  currentTime = TIO currentTime