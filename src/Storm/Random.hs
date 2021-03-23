module Storm.Random where

import qualified Control.Monad.Random          as Random

import           Storm.Core
import           Storm.Infrastructure

instance Random.MonadRandom TIO where
  getRandom   = TIO Random.getRandom
  getRandoms  = TIO Random.getRandoms
  getRandomR  = TIO . Random.getRandomR
  getRandomRs = TIO . Random.getRandomRs