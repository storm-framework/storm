module Binah.Random where

import qualified Control.Monad.Random          as Random

import           Binah.Core
import           Binah.Infrastructure

instance Random.MonadRandom TIO where
  getRandom   = TIO Random.getRandom
  getRandoms  = TIO Random.getRandoms
  getRandomR  = TIO . Random.getRandomR
  getRandomRs = TIO . Random.getRandomRs