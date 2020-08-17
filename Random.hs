module Binah.Random ( shuffleT ) where

import qualified Control.Monad.Random          as Random

import           Binah.Core
import           Binah.Infrastructure
import qualified System.Random.Shuffle         as Shuffle


instance Random.MonadRandom TIO where
  getRandom   = TIO Random.getRandom
  getRandoms  = TIO Random.getRandoms
  getRandomR  = TIO . Random.getRandomR
  getRandomRs = TIO . Random.getRandomRs

{-@ assume shuffleT :: [a] -> TaggedT<{\_ -> True}, {\_ -> False}> user m [a] @-}
shuffleT :: MonadTIO m => [a] -> TaggedT user m [a]
shuffleT = liftTIO . Shuffle.shuffleM