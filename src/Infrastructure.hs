{-# LANGUAGE FlexibleContexts, OverloadedStrings, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, GADTs, TypeFamilies, GeneralizedNewtypeDeriving, PartialTypeSignatures, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses #-}

module Infrastructure where


import Data.Functor.Const
import Data.Text (Text)
import Data.Aeson (ToJSON, FromJSON)
import Database.Persist hiding ((==.), (<-.), selectList, selectFirst, insert, entityKey, entityVal) --(PersistField, PersistValue, PersistEntity, Key, EntityField, Unique, Filter, fieldLens, Entity(Entity))
import qualified Database.Persist
import qualified Database.Persist.Sqlite
import qualified Database.Persist.TH
import qualified Data.Text
import qualified Data.Proxy
import qualified GHC.Int
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Data.Functor.Identity (Identity)
import Database.Persist.TH (mkPersist, sqlSettings, persistLowerCase)
import Database.Persist.Sql (SqlBackend, Migration)

import Data.Maybe (fromJust)

import Core
import Model

-- * Infrastructure
data TIO a = TIO { runTIO :: IO a }

instance Functor TIO where
  fmap f = TIO . fmap f . runTIO

instance Applicative TIO where
  pure = TIO . pure
  f <*> x = TIO $ runTIO f <*> runTIO x

instance Monad TIO where
  x >>= f = TIO $ runTIO x >>= (runTIO . f)

class Monad m => MonadTIO m where
  liftTIO :: TIO a -> m a

instance MonadTIO TIO where
  liftTIO = id

instance MonadTIO IO where
  liftTIO = runTIO

instance MonadTIO m => MonadTIO (ReaderT r m) where
  liftTIO = lift . liftTIO

instance MonadTIO m => MonadTIO (TaggedT m) where
  liftTIO = lift . liftTIO

{-@ data TaggedT m a <label :: Entity User -> Bool, clear :: Entity User -> Bool> = TaggedT _ @-}
data TaggedT m a = TaggedT { unTag :: m a }
{-@ data variance TaggedT invariant covariant contravariant covariant @-}

{- unTag :: TaggedT<{\_ -> True}, {\_ -> False}> m a -> m a -}

liftTaggedT :: Monad m => m a -> TaggedT m a
liftTaggedT = TaggedT

{-@ ignore mapTaggedT @-}
-- TODO: This causes LH crashes, but it also might be unsound re: security.
-- {-@ assume mapTaggedT :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. (m a -> n b) -> TaggedT<label, clear> m a -> TaggedT<label, clear> n b  @-}
mapTaggedT :: (m a -> n b) -> TaggedT m a -> TaggedT n b
mapTaggedT f = TaggedT . f . unTag

instance MonadTrans TaggedT where
  lift = liftTaggedT

instance MonadReader r m => MonadReader r (TaggedT m) where
  ask = lift ask
  local = mapTaggedT . local
  reader = lift . reader

-- TODO: Define this alias if/when LH allows abstract refinements in type aliases
-- {-@ type Tagged a label = TaggedT<label> Identity a @-}
-- type Tagged a = TaggedT Identity a

instance Functor m => Functor (TaggedT m) where
  fmap f = TaggedT . fmap f . unTag

instance Applicative m => Applicative (TaggedT m) where
  pure = TaggedT . pure
  f <*> x = TaggedT $ unTag f <*> unTag x

{-@
instance Monad m => Monad (TaggedT m) where
  >>= :: forall <p :: Entity User -> Bool, q :: Entity User -> Bool, r :: Entity User -> Bool, s :: Entity User -> Bool, t :: Entity User -> Bool, u :: Entity User -> Bool, rx :: a -> Bool, rf :: a -> b -> Bool, ro :: b -> Bool>.
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
