{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Binah.Infrastructure where

import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Data.Functor.Identity (Identity)

import Binah.Core

-- * Definitions
data TIO a = TIO { runTIO :: IO a }

class Monad m => MonadTIO m where
  liftTIO :: TIO a -> m a

{-@ data TaggedT user m a <label :: user -> Bool, clear :: user -> Bool> = TaggedT _ @-}
data TaggedT user m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant invariant covariant contravariant covariant @-}

-- TODO: Define this alias if/when LH allows abstract refinements in type aliases
-- {-@ type Tagged a label = TaggedT<label> user Identity a @-}
type Tagged user a = TaggedT user Identity a

-- * Functions
liftTaggedT :: Monad m => m a -> TaggedT user m a
liftTaggedT = TaggedT

{-@
assume mapTaggedT :: forall <label :: user -> Bool, clear :: user -> Bool>. _ -> TaggedT<label, clear> user _ _ -> TaggedT<label, clear> user _ _
@-}
mapTaggedT :: (m a -> n b) -> TaggedT user m a -> TaggedT user n b
mapTaggedT f x = TaggedT (f (unTag x))

-- * Instances

-- ** TIO Monad

instance Functor TIO where
  fmap f = TIO . fmap f . runTIO

instance Applicative TIO where
  pure = TIO . pure
  f <*> x = TIO $ runTIO f <*> runTIO x

instance Monad TIO where
  x >>= f = TIO $ runTIO x >>= (runTIO . f)

-- ** TaggedT Monad

-- TODO: Figure out the right types for fmap and <*>

{-@
instance Functor m => Functor (TaggedT user m) where
  fmap :: forall <p :: user -> Bool, q :: user -> Bool>.
    (a -> b) -> TaggedT<p, q> user m a -> TaggedT<p, q> user m b
@-}
instance Functor m => Functor (TaggedT user m) where
  fmap f = TaggedT . fmap f . unTag

{-@
instance Applicative m => Applicative (TaggedT user m) where
  pure :: a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a;
  <*> :: TaggedT user m (a -> b) -> TaggedT user m a -> TaggedT user m b
@-}
instance Applicative m => Applicative (TaggedT user m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT user m) where
  >>= :: forall <p :: user -> Bool, q :: user -> Bool, r :: user -> Bool, s :: user -> Bool, t :: user -> Bool, u :: user -> Bool, rx :: a -> Bool, rf :: a -> b -> Bool, ro :: b -> Bool>.
    {content :: a<rx> |- b<rf content> <: b<ro>}
    {content :: a<rx> |- b<ro> <: b<rf content>}
    {{v : (user<s>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<r>) | True}}
    {{v : (user<q>) | True} <: {v : (user<u>) | True}}
    {{v : (user<s>) | True} <: {v : (user<u>) | True}}
    x:TaggedT<p, q> user m (a<rx>) ->
    (y:a -> TaggedT<r, s> user m (b<rf y>)) ->
    TaggedT<t, u> user m (b<ro>);

  >> :: forall <p :: user -> Bool, q :: user -> Bool, r :: user -> Bool, s :: user -> Bool, t :: user -> Bool>.
    {{v : (user<q>) | True} <: {v : (user<t>) | True}}
    {{v : (user<s>) | True} <: {v : (user<t>) | True}}
    x:TaggedT<p, q> user m a ->
    TaggedT<r, s> user m b ->
    TaggedT<r, t> user m b;

  return :: a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a
@-}
instance Monad m => Monad (TaggedT user m) where
  x >>= f = TaggedT $ unTag x >>= (unTag . f)

-- For some reason LH ends up with `addC: malformed constraint:` if `return` is used in the TaggedT user monad.
-- Defining a function with the same signature solves the problem.
{-@ ignore returnTagged @-}
{-@ assume returnTagged:: a -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ _ @-}
returnTagged :: Monad m => a -> TaggedT user m a
returnTagged = return

-- ** MonadTIO

instance MonadTIO TIO where
  liftTIO = id

instance MonadTIO IO where
  liftTIO = runTIO

instance MonadTIO m => MonadTIO (ReaderT r m) where
  liftTIO x = lift (liftTIO x)

instance MonadTIO IO m => MonadTIO (TaggedT user m) where
  liftTIO x = lift (liftTIO x)

-- Monad Transformers

instance MonadTrans (TaggedT user) where
  lift = liftTaggedT

instance MonadReader r m => MonadReader r (TaggedT user m) where
  ask = lift ask
  local = mapTaggedT . local
  reader x = lift (reader x)
