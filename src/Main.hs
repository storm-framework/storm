{-# LANGUAGE FlexibleContexts, OverloadedStrings, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, GADTs, TypeFamilies, GeneralizedNewtypeDeriving, PartialTypeSignatures, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses #-}
{-@ LIQUID "--no-pattern-inline" @-}
module Main where

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
{-@ mapTaggedT :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. (m a -> n b) -> TaggedT<label, clear> m a -> TaggedT<label, clear> n b  @-}
mapTaggedT :: (m a -> n b) -> TaggedT m a -> TaggedT n b
mapTaggedT f = TaggedT . f . unTag

instance MonadTrans TaggedT where
  lift = liftTaggedT

instance MonadReader r m => MonadReader r (TaggedT m) where
  ask = lift ask
  local = mapTaggedT . local
  reader = lift . reader

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

{-@ data RefinedFilter record <r :: Entity record -> Bool, q :: Entity record -> Entity User -> Bool> = RefinedFilter _ @-}
data RefinedFilter record = RefinedFilter (Filter record)

{-@ data variance RefinedFilter covariant covariant contravariant @-}

{-@
(Main.==.) ::
forall <policy :: Entity record -> Entity User -> Bool,
       selector :: Entity record -> typ -> Bool,
       inverseselector :: typ -> Entity record -> Bool,
       fieldfilter :: typ -> Bool,
       filter :: Entity record -> Bool,
       r :: typ -> Bool>.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
  { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }
  EntityFieldWrapper<policy, selector, inverseselector> record typ -> typ<r> -> RefinedFilter<filter, policy> record
@-}
(==.) :: PersistField typ => EntityFieldWrapper record typ -> typ -> RefinedFilter record
(EntityFieldWrapper field) ==. value = RefinedFilter (field Database.Persist.==. value)

{-@
(Main.<-.) ::
forall <policy :: Entity record -> Entity User -> Bool,
       selector :: Entity record -> typ -> Bool,
       inverseselector :: typ -> Entity record -> Bool,
       fieldfilter :: typ -> Bool,
       filter :: Entity record -> Bool,
       r :: typ -> Bool>.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
  { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }
  EntityFieldWrapper<policy, selector, inverseselector> record typ -> [typ<r>] -> RefinedFilter<filter, policy> record
@-}
(<-.) :: PersistField typ => EntityFieldWrapper record typ -> [typ] -> RefinedFilter record
(EntityFieldWrapper field) <-. value = RefinedFilter (field Database.Persist.<-. value)

{-@
data FilterList record <q :: Entity record -> Entity User -> Bool, r :: Entity record -> Bool> where
    Empty :: FilterList<{\_ _ -> True}, {\_ -> True}> record
  | Cons :: RefinedFilter<{\_ -> True}, {\_ _ -> False}> record ->
            FilterList<{\_ _ -> False}, {\_ -> True}> record ->
            FilterList<q, r> record
@-}
{-@ data variance FilterList covariant contravariant covariant @-}
data FilterList a = Empty | Cons (RefinedFilter a) (FilterList a)

-- Don't use `Cons` to construct FilterLists: only ever use `?:`. This should be
-- enforced by not exporting `Cons`.

infixr 5 ?:
{-@
(?:) :: forall <r :: Entity record -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool,
                q :: Entity record -> Entity User -> Bool, q1 :: Entity record -> Entity User -> Bool, q2 :: Entity record -> Entity User -> Bool>.
  {row1 :: (Entity <r1> record), row2 :: (Entity <r2> record) |- {v:Entity record | v == row1 && v == row2} <: {v:(Entity <r> record) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q1 row> User) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q2 row> User) | True}}
  RefinedFilter<r1, q1> record ->
  FilterList<q2, r2> record ->
  FilterList<q, r> record
@-}
(?:) :: RefinedFilter record -> FilterList record -> FilterList record
f ?: fs = f `Cons` fs

{-@ ignore selectList @-}
{-@
assume selectList :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  FilterList<q, r1> record -> TaggedT<p, {\_ -> False}> _ [(Entity <r2> record)]
@-}
selectList :: forall backend record m. (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => FilterList record -> TaggedT m [Entity record]
selectList filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Database.Persist.selectList (toPersistFilters filters) []) backend
  where
    toPersistFilters Empty = []
    toPersistFilters (RefinedFilter f `Cons` filters) = f:(toPersistFilters filters)

{-@ ignore selectFirst @-}
{-@
assume selectFirst :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  FilterList<q, r1> record -> TaggedT<p, {\_ -> False}> _ (Maybe (Entity <r2> record))
@-}
selectFirst :: forall backend record m. (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => FilterList record -> TaggedT m (Maybe (Entity record))
selectFirst filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Database.Persist.selectFirst (toPersistFilters filters) []) backend
  where
    toPersistFilters Empty = []
    toPersistFilters (RefinedFilter f `Cons` filters) = f:(toPersistFilters filters)

{-@
assume projectList :: forall <r1 :: Entity record -> Bool, r2 :: typ -> Bool, policy :: Entity record -> Entity User -> Bool, p :: Entity User -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool>.
  { row :: (Entity <r1> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <policy row> User) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  EntityFieldWrapper<policy, selector, inverseselector> record typ ->
  [(Entity <r1> record)] ->
  TaggedT<p, {\_ -> False}> _ [typ<r2>]
@-}
projectList :: (PersistEntity record, Applicative m) => EntityFieldWrapper record typ -> [Entity record] -> TaggedT m [typ]
projectList (EntityFieldWrapper entityField) entities = pure $ map (\x -> getConst $ fieldLens entityField Const x) entities

-- -- * Outputs

{-@
assume printTo :: user:_ -> _ -> TaggedT<{\_ -> True}, {\viewer -> viewer == user}> _ ()
@-}
printTo :: MonadTIO m => Entity User -> String -> TaggedT m ()
printTo user str = liftTIO . TIO . putStrLn . mconcat $
  ["[", userName . entityVal $ user, "] ", str]

-- * Client code
{-@ measure Main.id1 :: Key User @-}
{-@ assume id1 :: {v:Key User | v == id1} @-}
id1 :: Key User
id1 = UserKey undefined

{-@ combinatorExample1 :: RefinedFilter<{\row -> userName (entityVal row) == "alice"}, {\row v -> entityKey v == entityKey row}> User @-}
combinatorExample1 :: RefinedFilter User
combinatorExample1 = userNameField ==. "alice"

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = Empty

-- {-@ exampleList2 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1}> User @-}
-- exampleList2 :: FilterList User
-- exampleList2 = (userFriendField ==. id1) ?: Empty

-- {-@ exampleList3 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- exampleList3 :: FilterList User
-- exampleList3 = userNameField ==. "alice" ?: userFriendField ==. id1 ?: Empty

-- {-@ exampleList4 :: FilterList<{\_ v -> entityKey v == id1}, {\user -> userFriend (entityVal user) == id1 && userName (entityVal user) == "alice"}> User @-}
-- exampleList4 :: FilterList User
-- exampleList4 = userFriendField ==. id1 ?: userNameField ==. "alice" ?: Empty

{-@ exampleList5 :: FilterList<{\row v -> entityKey v == entityKey row}, {\user -> userName (entityVal user) == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = userNameField ==. "alice" ?: Empty

-- {-@ exampleSelectList1 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : Entity User | userFriend (entityVal v) == id1}] @-}
-- exampleSelectList1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- exampleSelectList1 = selectList filters
--   where
--     {-@ filters :: FilterList<{\_ v -> entityKey v == id1}, {\v -> userFriend (entityVal v) == id1}> User @-}
--     filters = userFriendField ==. id1 ?: Empty

-- {-@ exampleSelectList2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v : _ | userFriend (entityVal v) == id1 && userName (entityVal v) == "alice"}] @-}
-- exampleSelectList2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- exampleSelectList2 = selectList (userNameField ==. "alice" ?: userFriendField ==. id1 ?: Empty)

{-@ exampleSelectList3 :: TaggedT<{\_ -> False}, {\_ -> False}> _ [{v : _ | userName (entityVal v) == "alice"}] @-}
exampleSelectList3 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
exampleSelectList3 = selectList (userNameField ==. "alice" ?: Empty)

-- {-@ projectSelect1 :: [{v:_ | userFriend (entityVal v) == id1}] -> TaggedT<{\_ -> False}, {\_ -> False}> Identity [{v:_ | len v == 9}] @-}
-- projectSelect1 :: [Entity User] -> TaggedT Identity [String]
-- projectSelect1 users = projectList userSSNField users

-- -- | This is fine: user 1 can see both the filtered rows and the name field in
-- --   each of these rows
-- {-@ names :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [String] @-}
-- names :: TaggedT (ReaderT SqlBackend TIO) [String]
-- names = do
--   rows <- selectList (userFriendField ==. id1 ?: Empty)
--   projectList userNameField rows

-- -- | This is bad: the result of the query is not public
-- {-@ bad1 :: TaggedT<{\v -> True}, {\_ -> False}> _ [{v: _ | userFriend (entityVal v) == id1}]
-- @-}
-- bad1 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
-- bad1 = selectList (userFriendField ==. id1 ?: Empty)

-- | This is bad: who knows who else has name "alice" and is not friends with user 1?
{-@ bad2 :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v: _ | userName (entityVal v) == "alice"}]
@-}
bad2 :: TaggedT (ReaderT SqlBackend TIO) [Entity User]
bad2 = selectList (userNameField ==. "alice" ?: Empty)

-- -- | This is bad: user 1 can see the filtered rows but not their SSNs
-- {-@ badSSNs :: TaggedT<{\v -> entityKey v == id1}, {\_ -> False}> _ [{v:_ | len v == 9}]
-- @-}
-- badSSNs :: TaggedT (ReaderT SqlBackend TIO) [String]
-- badSSNs = do
--   rows <- selectList (userFriendField ==. id1 ?: Empty)
--   projectList userSSNField rows -- bad

{-@
getSharedTasks :: u:_ -> TaggedT<{\viewer -> entityKey viewer == u}, {\_ -> False}> _ [{v:_ | len v > 0}]
@-}
getSharedTasks :: Key User -> TaggedT (ReaderT SqlBackend TIO) [String]
getSharedTasks userKey = do
  shares <- selectList (shareToField ==. userKey ?: Empty)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  projectList todoItemTaskField sharedTodoItems

{-@
preserveInvariant :: TaggedT<{\viewer -> True}, {\_ -> False}> _ [Entity {s:Share | shared (shareFrom s) (shareTo s)}]
@-}
preserveInvariant :: TaggedT (ReaderT SqlBackend TIO) [Entity Share]
preserveInvariant = selectList filters
  where
    {-@ filters :: FilterList<{\_ _ -> True}, {\_ -> True}> {s:Share | shared (shareFrom s) (shareTo s)} @-}
    filters :: FilterList Share
    filters = Empty

{-@ action1 :: TaggedT<{\viewer -> False}, {\recipient -> False}> _ _ @-}
action1 :: TaggedT TIO ()
action1 = undefined

{-@ action2 :: _ -> TaggedT<{\viewer -> True}, {\recipient -> True}> _ _ @-}
action2 :: a -> TaggedT TIO a
action2 = undefined

{-@ action3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
action3 :: TaggedT TIO ()
action3 = undefined

{-@ testBind1 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind1 = action1 >>= action2 -- bad

{-@ testBind2 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind2 = action3 >>= \_ -> action3 -- bad

{-@ testBind3 :: TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
testBind3 = action3 >> action3

{-@
getSharedTasksBad :: _ -> TaggedT<{\viewer -> True}, {\_ -> False}> _ _
@-}
getSharedTasksBad :: Key User -> TaggedT (ReaderT SqlBackend TIO) [String]
getSharedTasksBad userKey = do
  shares <- selectList Empty
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  projectList todoItemTaskField sharedTodoItems -- bad

{-@ consumeTagged :: forall <label :: Entity User -> Bool, clear :: Entity User -> Bool>. TaggedT<label, clear> m a -> b @-}
consumeTagged :: TaggedT m a -> b
consumeTagged _ = undefined

{-@ ignore specialReturn @-}
{-@ assume specialReturn :: a -> TaggedT<{\_ -> True}, {\_ -> False}> m a @-}
specialReturn :: Monad m => a -> TaggedT m a
specialReturn = return -- TODO: why does normal return not work?

{-@ printSharedTasks'' :: u:_ -> RefinedFilter<{\sh -> shareTo (entityVal sh) == entityKey u}, {\_ _ -> False}> _ @-}
printSharedTasks'' :: Entity User -> RefinedFilter Share
printSharedTasks'' user = shareToField ==. entityKey user

{-@ printSharedTasks' :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ [{v: Entity Share | shareTo (entityVal v) == entityKey u}] @-}
printSharedTasks' :: Entity User -> TaggedT (ReaderT SqlBackend TIO) [Entity Share]
printSharedTasks' user = do
  selectList (shareToField ==. entityKey user ?: Empty)


{-@ printSharedTasks :: u:_ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
printSharedTasks :: Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedTasks user = do
  shares <- selectList (shareToField ==. entityKey user ?: Empty)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  tasks <- projectList todoItemTaskField sharedTodoItems
  printTo user $ show tasks

{-@ printSharedTasksBad :: _ -> _ -> TaggedT<{\viewer -> False}, {\recipient -> True}> _ _ @-}
printSharedTasksBad :: Entity User -> Entity User -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedTasksBad user1 user2 = do
  shares <- selectList (shareToField ==. entityKey user1 ?: Empty)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  tasks <- projectList todoItemTaskField sharedTodoItems -- bad
  printTo user2 $ show tasks -- bad


runSqlite :: Text -> ReaderT SqlBackend TIO a -> TIO a
runSqlite connStr action = TIO . Database.Persist.Sqlite.runSqlite connStr $ do
  backend <- ask
  liftIO . runTIO . (`runReaderT` backend) $ action

runMigration :: (MonadTIO m, MonadReader SqlBackend m) => Migration -> m ()
runMigration migration = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Database.Persist.Sqlite.runMigration migration

insert :: (PersistStoreWrite backend, PersistRecordBackend record backend, MonadTIO m, MonadReader backend m) => record -> m (Key record)
insert record = do
  backend <- ask
  liftTIO . TIO . (`runReaderT` backend) $ Database.Persist.insert record

{-@ ignore main @-}
main :: IO ()
main = runTIO . unTag $ taggedMain

setupDB :: ReaderT SqlBackend TIO (UserId, UserId)
setupDB = do
  runMigration migrateAll

  aliceId <- insert $ User "Alice" "123456789"
  bobId <- insert $ User "Bob" "987654321"

  insert $ TodoItem bobId "Get groceries"
  insert $ TodoItem bobId "Vacuum"
  insert $ TodoItem aliceId "Submit paper"

  insert $ Share bobId aliceId

  return (aliceId, bobId)

{-@ taggedMain :: TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
taggedMain ::  TaggedT TIO ()
taggedMain = mapTaggedT (runSqlite ":memory:") $ do
  (aliceId, bobId) <- lift setupDB
  printSharedWith aliceId
  printSharedWith bobId

{-@ printSharedWith :: _ -> TaggedT<{\_ -> False}, {\_ -> True}> _ _ @-}
printSharedWith :: UserId -> TaggedT (ReaderT SqlBackend TIO) ()
printSharedWith userId = do
  user <- fromJust <$> selectFirst (userIdField ==. userId ?: Empty)
  shares <- selectList (shareToField ==. entityKey user ?: Empty)
  sharedFromUsers <- projectList shareFromField shares
  sharedTodoItems <- selectList (todoItemOwnerField <-. sharedFromUsers ?: Empty)
  tasks <- projectList todoItemTaskField sharedTodoItems
  printTo user $ show tasks
