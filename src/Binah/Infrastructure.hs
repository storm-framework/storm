{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Binah.Infrastructure where

import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Data.Functor.Identity (Identity)

import Binah.Core
import Model

-- * Definitions
data TIO a = TIO { runTIO :: IO a }

class Monad m => MonadTIO m where
  liftTIO :: TIO a -> m a

{-@ data TaggedT m a <label :: Entity User -> Bool, clear :: Entity User -> Bool> = TaggedT _ @-}
data TaggedT m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant covariant contravariant covariant @-}

-- TODO: Define this alias if/when LH allows abstract refinements in type aliases
-- {-@ type Tagged a label = TaggedT<label> Identity a @-}
type Tagged a = TaggedT Identity a

-- * Functions
liftTaggedT :: Monad m => m a -> TaggedT m a
liftTaggedT = TaggedT

{-@
assume mapTaggedT :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. _ -> TaggedT<label, clear> _ _ -> TaggedT<label, clear> _ _
@-}
mapTaggedT :: (m a -> n b) -> TaggedT m a -> TaggedT n b
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
instance Functor m => Functor (TaggedT m) where
  fmap :: forall <p :: Entity User -> Bool, q :: Entity User -> Bool>.
    (a -> b) -> TaggedT<p, q> m a -> TaggedT<p, q> m b
@-}
instance Functor m => Functor (TaggedT m) where
  fmap f = TaggedT . fmap f . unTag

{-@
instance Applicative m => Applicative (TaggedT m) where
  pure :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a;
  <*> :: TaggedT m (a -> b) -> TaggedT m a -> TaggedT m b
@-}
instance Applicative m => Applicative (TaggedT m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT m) where
  >>= :: forall <p :: Entity User -> Bool, q :: Entity User -> Bool, r :: Entity User -> Bool, s :: Entity User -> Bool, t :: Entity User -> Bool, u :: Entity User -> Bool, rx :: a -> Bool, rf :: a -> b -> Bool, ro :: b -> Bool>.
    {content :: a<rx> |- b<rf content> <: b<ro>}
    {content :: a<rx> |- b<ro> <: b<rf content>}
    {{v : (Entity<s> User) | True} <: {v : (Entity<p> User) | True}}
    {{v : (Entity<t> User) | True} <: {v : (Entity<p> User) | True}}
    {{v : (Entity<t> User) | True} <: {v : (Entity<r> User) | True}}
    {{v : (Entity<q> User) | True} <: {v : (Entity<u> User) | True}}
    {{v : (Entity<s> User) | True} <: {v : (Entity<u> User) | True}}
    x:TaggedT<p, q> m (a<rx>) ->
    (y:a -> TaggedT<r, s> m (b<rf y>)) ->
    TaggedT<t, u> m (b<ro>);

  >> :: forall <p :: Entity User -> Bool, q :: Entity User -> Bool, r :: Entity User -> Bool, s :: Entity User -> Bool, t :: Entity User -> Bool>.
    {{v : (Entity<q> User) | True} <: {v : (Entity<t> User) | True}}
    {{v : (Entity<s> User) | True} <: {v : (Entity<t> User) | True}}
    x:TaggedT<p, q> m a ->
    TaggedT<r, s> m b ->
    TaggedT<r, t> m b;

  return :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a
@-}
instance Monad m => Monad (TaggedT m) where
  x >>= f = TaggedT $ unTag x >>= (unTag . f)

-- For some reason LH ends up with `addC: malformed constraint:` if `return` is used in the TaggedT monad.
-- Defining a function with the same signature solves the problem.
{-@ ignore returnTagged @-}
{-@ assume returnTagged:: a -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
returnTagged :: Monad m => a -> TaggedT m a
returnTagged = return

-- ** MonadTIO

instance MonadTIO TIO where
  liftTIO = id

instance MonadTIO IO where
  liftTIO = runTIO

instance MonadTIO m => MonadTIO (ReaderT r m) where
  liftTIO x = lift (liftTIO x)

instance MonadTIO m => MonadTIO (TaggedT m) where
  liftTIO x = lift (liftTIO x)

-- Monad Transformers

instance MonadTrans TaggedT where
  lift = liftTaggedT

instance MonadReader r m => MonadReader r (TaggedT m) where
  ask = lift ask
  local = mapTaggedT . local
  reader x = lift (reader x)
