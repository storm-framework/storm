{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Storm.Infrastructure where

import           Control.Monad.Trans.Class      ( MonadTrans(..) )
import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , ReaderT(..)
                                                )
import           Control.Monad                  ( when
                                                , replicateM
                                                )
import           Data.Functor.Identity          ( Identity )

import           Storm.Core

-- * Definitions
data TIO a = TIO { runTIO :: IO a }

class Monad m => MonadTIO m where
  liftTIO :: TIO a -> m a

{-@ data TaggedT user m a <label :: user -> Bool, clear :: user -> Bool> = TaggedT _ @-}
data TaggedT user m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant invariant covariant contravariant covariant @-}

-- * Functions
{-@ liftT :: m a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a @-}
liftT :: Monad m => m a -> TaggedT user m a
liftT = TaggedT

{-@ assume mapTaggedT :: forall <label :: user -> Bool, clear :: user -> Bool>.
                           _ -> TaggedT<label, clear> user _ _ -> TaggedT<label, clear> user _ _
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

-- TODO: Figure sink the right types for fmap and <*>

{-@
instance Functor m => Functor (TaggedT user m) where
  fmap :: forall <p :: user -> Bool, q :: user -> Bool>.
    (a -> b) -> TaggedT<p, q> user m a -> TaggedT<p, q> user m b
@-}
instance Functor m => Functor (TaggedT user m) where
  fmap f = TaggedT . fmap f . unTag

{-@
instance Applicative m => Applicative (TaggedT user m) where
  pure :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a;
  <*> :: forall <p :: user -> Bool, q :: user -> Bool>.
    TaggedT<p, q> user m (a -> b) -> TaggedT<p, q> user m a -> TaggedT<p, q> user m b
@-}
instance Applicative m => Applicative (TaggedT user m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT user m) where
  >>= :: forall < p :: user -> Bool
                , q :: user -> Bool
                , r :: user -> Bool
                , s :: user -> Bool
                , t :: user -> Bool
                , u :: user -> Bool
                , rx :: a -> Bool
                , rf :: a -> b -> Bool
                , ro :: b -> Bool
                >.
    {content :: a<rx> |- b<rf content> <: b<ro>}
    {content :: a<rx> |- b<ro> <: b<rf content>}
    {{v : (user<s>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<p>) | True}}
    {{v : (user<t>) | True} <: {v : (user<r>) | True}}
    {{v : (user<q>) | True} <: {v : (user<u>) | True}}
    {{v : (user<s>) | True} <: {v : (user<u>) | True}}
    x:TaggedT<p, q> user m (a<rx>)
    -> (y:a -> TaggedT<r, s> user m (b<rf y>))
    -> TaggedT<t, u> user m (b<ro>);

  >> :: forall < p :: user -> Bool
               , q :: user -> Bool
               , r :: user -> Bool
               , s :: user -> Bool
               , t :: user -> Bool
               >.
    {{v : (user<q>) | True} <: {v : (user<t>) | True}}
    {{v : (user<s>) | True} <: {v : (user<t>) | True}}
    x:TaggedT<p, q> user m a
    -> TaggedT<r, s> user m b
    -> TaggedT<r, t> user m b;

  return :: a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a
@-}
instance Monad m => Monad (TaggedT user m) where
  x >>= f = TaggedT $ unTag x >>= (unTag . f)

-- For some reason LH ends up with `addC: malformed constraint:` if `return` is used in the TaggedT monad.
-- Defining a function with the same signature solves the problem.
{-@ ignore returnTagged @-}
{-@ assume returnTagged:: a -> TaggedT<{\_ -> True}, {\_ -> False}> user _ _ @-}
returnTagged :: Monad m => a -> TaggedT user m a
returnTagged = return

-- Monad Transformers

instance MonadTrans (TaggedT user) where
  lift = liftT

instance MonadReader r m => MonadReader r (TaggedT user m) where
  ask   = lift ask
  local = mapTaggedT . local
  reader x = lift (reader x)

-- ** MonadTIO

instance MonadTIO TIO where
  liftTIO = id

instance MonadTIO IO where
  liftTIO = runTIO

instance MonadTIO m => MonadTIO (ReaderT r m) where
  liftTIO x = lift (liftTIO x)


{-@
instance MonadTIO m => MonadTIO (TaggedT user m) where
  liftTIO :: TIO a -> TaggedT<{\_ -> True}, {\_ -> False}> user m a
@-}
instance MonadTIO m => MonadTIO (TaggedT user m) where
  liftTIO x = liftT (liftTIO x)


-- ** Properly polymorphic function for TaggedT

{-@ ignore mapT @-}
{-@
mapT :: forall <source :: user -> Bool, sink :: user -> Bool>.
  (a -> TaggedT<source, sink> user m b) -> [a] -> TaggedT<source, sink> user m [b]
@-}
mapT :: MonadTIO m => (a -> TaggedT user m b) -> [a] -> TaggedT user m [b]
mapT = mapM

{-@ forT :: forall <source :: user -> Bool, sink :: user -> Bool>.
              [a] -> (a -> TaggedT<source, sink> user m b) -> TaggedT<source, sink> user m [b]
@-}
forT :: MonadTIO m => [a] -> (a -> TaggedT user m b) -> TaggedT user m [b]
forT = flip mapT

{-@
assume whenT :: forall <source :: user -> Bool, sink :: user -> Bool>.
  Bool -> TaggedT<source, sink> user m () -> TaggedT<source, sink> user m ()
@-}
whenT :: Applicative m => Bool -> TaggedT user m () -> TaggedT user m ()
whenT = when

{-@
assume replicateT :: forall <source :: user -> Bool, sink :: user -> Bool>.
  Int -> TaggedT<source, sink> user m a -> TaggedT<source, sink> user m [a]
@-}
replicateT :: Applicative m => Int -> TaggedT user m a -> TaggedT user m [a]
replicateT = replicateM

{-@
assume mapMaybeT :: forall <source :: user -> Bool, sink :: user -> Bool>.
  (a -> TaggedT<source, sink> user m (Maybe b)) -> [a] -> TaggedT<source, sink> user m [b]
@-}
mapMaybeT :: MonadTIO m => (a -> TaggedT user m (Maybe b)) -> [a] -> TaggedT user m [b]
mapMaybeT _ []     = return []
mapMaybeT f (a:as) = do
  b  <- f a
  bs <- mapMaybeT f as
  case b of
    Just b  -> return (b : bs)
    Nothing -> return bs