{-# LANGUAGE FlexibleContexts, OverloadedStrings, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, GADTs, TypeFamilies, GeneralizedNewtypeDeriving, PartialTypeSignatures, QuasiQuotes, TemplateHaskell, MultiParamTypeClasses #-}
{-@ LIQUID "--no-pattern-inline" @-}
module Main where

import Data.Functor.Const
import Data.Text (Text)
import Data.Aeson (ToJSON, FromJSON)
import Database.Persist hiding ((==.), (<-.), selectList, selectFirst, entityKey, entityVal, insert) --(PersistField, PersistValue, PersistEntity, Key, EntityField, Unique, Filter, fieldLens, Entity(Entity))
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

-- * Models
-- class PersistEntity record where
--   data Key record
--   data EntityField record :: * -> *
--   data Unique record

--   keyToValues :: Key record -> [PersistValue]
--   keyFromValues :: [PersistValue] -> Either Text (Key record)
--   persistIdField :: EntityField record (Key record)

{-@
data EntityFieldWrapper record typ <policy :: Entity record -> Entity User -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool> = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant contravariant invariant invariant @-}

{-@ measure entityKey @-}
entityKey :: Entity record -> Key record
entityKey (Entity key _) = key

{-@ measure entityVal @-}
entityVal :: Entity record -> record
entityVal (Entity _ val) = val

-- {-@
-- data Entity record = Entity
--   { entityKey :: _
--   , entityVal :: _
--   }
-- @-}
-- data Entity record = Entity
--   { entityKey :: Key record
--   , entityVal :: record
--   }

-- ** User
{-@
data User = User
  { userName :: _
  , userSSN :: {v:_ | len v == 9}
  }
@-}

-- data User = User
--   { userName :: String
--   , userFriend :: Key User
--   , userSSN :: String
--   } deriving (Eq, Show)

-- instance PersistEntity User where
--   newtype Key User = UserKey Int
--     deriving (PersistField, ToJSON, FromJSON, Show, Read, Eq, Ord)

--   data EntityField User typ where
--     UserId :: EntityField User (Key User)
--     UserName :: EntityField User String
--     UserFriend :: EntityField User (Key User)
--     UserSSN :: EntityField User String

--   data Unique User

--   keyToValues = undefined
--   keyFromValues = undefined
--   persistIdField = UserId

-- TODO: This complains about fromPersistValues, which is legitimate. What should we do?

Database.Persist.TH.share [mkPersist sqlSettings, Database.Persist.TH.mkMigrate "migrateAll"] [persistLowerCase|
User
  name String
  sSN String

TodoItem
  owner UserId
  task String

Share
  from UserId
  to UserId
|]


-- mapLeft :: (a -> b) -> Either a c -> Either b c
-- mapLeft _ (Right x) = Right x
-- mapLeft f (Left x) = Left (f x)

-- headNote :: [b] -> b
-- headNote = head

-- fieldError :: Text -> a -> Text
-- fieldError err _ = err

-- data User = User {userName :: !String,
--               userFriend :: !(Key User),
--               userSSN :: !String}
--       deriving ()
-- type UserId = Key User
-- instance PersistEntity User where
--   type PersistEntityBackend User = Database.Persist.Sqlite.SqlBackend
--   data Unique User
--   newtype Key User
--     = UserKey {unUserKey :: (Database.Persist.Sqlite.BackendKey Database.Persist.Sqlite.SqlBackend)}
--     deriving (Show,
--               Read,
--               Eq,
--               Ord,
--               PersistField,
--               ToJSON,
--               FromJSON)
--   data EntityField User typ
--     = typ ~ Key User => UserId |
--       typ ~ String => UserName |
--       typ ~ Key User => UserFriend |
--       typ ~ String => UserSSN
--   keyToValues
--     = ((: []) . (Database.Persist.Sqlite.toPersistValue . unUserKey))
--   keyFromValues
--     = (fmap UserKey
--          . (Database.Persist.Sqlite.fromPersistValue
--               . headNote))
--   entityDef _
--     = (((((((((Database.Persist.Sqlite.EntityDef
--                  (Database.Persist.Sqlite.HaskellName
--                     (Database.Persist.TH.packPTH "User")))
--                 (Database.Persist.Sqlite.DBName
--                    (Database.Persist.TH.packPTH "user")))
--                (((((((Database.Persist.Sqlite.FieldDef
--                         (Database.Persist.Sqlite.HaskellName
--                            (Database.Persist.TH.packPTH "Id")))
--                        (Database.Persist.Sqlite.DBName
--                           (Database.Persist.TH.packPTH "id")))
--                       ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                          (Database.Persist.TH.packPTH "UserId")))
--                      Database.Persist.Sqlite.SqlInt64)
--                     [])
--                    True)
--                   ((Database.Persist.Sqlite.ForeignRef
--                       (Database.Persist.Sqlite.HaskellName
--                          (Database.Persist.TH.packPTH "User")))
--                      ((Database.Persist.Sqlite.FTTypeCon
--                          (Just (Database.Persist.TH.packPTH "Data.Int")))
--                         (Database.Persist.TH.packPTH "Int64")))))
--               [])
--              [((((((Database.Persist.Sqlite.FieldDef
--                       (Database.Persist.Sqlite.HaskellName
--                          (Database.Persist.TH.packPTH "name")))
--                      (Database.Persist.Sqlite.DBName
--                         (Database.Persist.TH.packPTH "name")))
--                     ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                        (Database.Persist.TH.packPTH "String")))
--                    Database.Persist.Sqlite.SqlString)
--                   [])
--                  True)
--                 Database.Persist.Sqlite.NoReference,
--               ((((((Database.Persist.Sqlite.FieldDef
--                       (Database.Persist.Sqlite.HaskellName
--                          (Database.Persist.TH.packPTH "friend")))
--                      (Database.Persist.Sqlite.DBName
--                         (Database.Persist.TH.packPTH "friend")))
--                     ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                        (Database.Persist.TH.packPTH "UserId")))
--                    (Database.Persist.Sqlite.sqlType
--                       (Data.Proxy.Proxy :: Data.Proxy.Proxy GHC.Int.Int64)))
--                   [])
--                  True)
--                 ((Database.Persist.Sqlite.ForeignRef
--                     (Database.Persist.Sqlite.HaskellName
--                        (Database.Persist.TH.packPTH "User")))
--                    ((Database.Persist.Sqlite.FTTypeCon
--                        (Just (Database.Persist.TH.packPTH "Data.Int")))
--                       (Database.Persist.TH.packPTH "Int64"))),
--               ((((((Database.Persist.Sqlite.FieldDef
--                       (Database.Persist.Sqlite.HaskellName
--                          (Database.Persist.TH.packPTH "sSN")))
--                      (Database.Persist.Sqlite.DBName
--                         (Database.Persist.TH.packPTH "s_s_n")))
--                     ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                        (Database.Persist.TH.packPTH "String")))
--                    Database.Persist.Sqlite.SqlString)
--                   [])
--                  True)
--                 Database.Persist.Sqlite.NoReference])
--             [])
--            [])
--           [])
--          (Data.Map.Internal.fromList []))
--         False
--   toPersistFields (User x_a8yr x_a8ys x_a8yt)
--     = [Database.Persist.Sqlite.SomePersistField x_a8yr,
--        Database.Persist.Sqlite.SomePersistField x_a8ys,
--        Database.Persist.Sqlite.SomePersistField x_a8yt]
--   fromPersistValues
--     [x1_a8yv, x2_a8yw, x3_a8yx]
--     = User
--         <$>
--           (mapLeft
--              (fieldError
--                 (Database.Persist.TH.packPTH "name"))
--              . Database.Persist.Sqlite.fromPersistValue)
--             x1_a8yv
--         <*>
--           (mapLeft
--              (fieldError
--                 (Database.Persist.TH.packPTH "friend"))
--              . Database.Persist.Sqlite.fromPersistValue)
--             x2_a8yw
--         <*>
--           (mapLeft
--              (fieldError
--                 (Database.Persist.TH.packPTH "sSN"))
--              . Database.Persist.Sqlite.fromPersistValue)
--             x3_a8yx
--   fromPersistValues x_a8yu
--     = (Left
--          $ (mappend
--               (Database.Persist.TH.packPTH
--                  "User: fromPersistValues failed on: "))
--              (Data.Text.pack $ show x_a8yu))
--   persistUniqueToFieldNames _
--     = error "Degenerate case, should never happen"
--   persistUniqueToValues _
--     = error "Degenerate case, should never happen"
--   persistUniqueKeys
--     (User _name_a8yy _friend_a8yz _sSN_a8yA)
--     = []
--   persistFieldDef UserId
--     = ((((((Database.Persist.Sqlite.FieldDef
--               (Database.Persist.Sqlite.HaskellName
--                  (Database.Persist.TH.packPTH "Id")))
--              (Database.Persist.Sqlite.DBName
--                 (Database.Persist.TH.packPTH "id")))
--             ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                (Database.Persist.TH.packPTH "UserId")))
--            Database.Persist.Sqlite.SqlInt64)
--           [])
--          True)
--         ((Database.Persist.Sqlite.ForeignRef
--             (Database.Persist.Sqlite.HaskellName
--                (Database.Persist.TH.packPTH "User")))
--            ((Database.Persist.Sqlite.FTTypeCon
--                (Just (Database.Persist.TH.packPTH "Data.Int")))
--               (Database.Persist.TH.packPTH "Int64")))
--   persistFieldDef UserName
--     = ((((((Database.Persist.Sqlite.FieldDef
--               (Database.Persist.Sqlite.HaskellName
--                  (Database.Persist.TH.packPTH "name")))
--              (Database.Persist.Sqlite.DBName
--                 (Database.Persist.TH.packPTH "name")))
--             ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                (Database.Persist.TH.packPTH "String")))
--            Database.Persist.Sqlite.SqlString)
--           [])
--          True)
--         Database.Persist.Sqlite.NoReference
--   persistFieldDef UserFriend
--     = ((((((Database.Persist.Sqlite.FieldDef
--               (Database.Persist.Sqlite.HaskellName
--                  (Database.Persist.TH.packPTH "friend")))
--              (Database.Persist.Sqlite.DBName
--                 (Database.Persist.TH.packPTH "friend")))
--             ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                (Database.Persist.TH.packPTH "UserId")))
--            Database.Persist.Sqlite.SqlInt64)
--           [])
--          True)
--         ((Database.Persist.Sqlite.ForeignRef
--             (Database.Persist.Sqlite.HaskellName
--                (Database.Persist.TH.packPTH "User")))
--            ((Database.Persist.Sqlite.FTTypeCon
--                (Just (Database.Persist.TH.packPTH "Data.Int")))
--               (Database.Persist.TH.packPTH "Int64")))
--   persistFieldDef UserSSN
--     = ((((((Database.Persist.Sqlite.FieldDef
--               (Database.Persist.Sqlite.HaskellName
--                  (Database.Persist.TH.packPTH "sSN")))
--              (Database.Persist.Sqlite.DBName
--                 (Database.Persist.TH.packPTH "s_s_n")))
--             ((Database.Persist.Sqlite.FTTypeCon Nothing)
--                (Database.Persist.TH.packPTH "String")))
--            Database.Persist.Sqlite.SqlString)
--           [])
--          True)
--         Database.Persist.Sqlite.NoReference
--   persistIdField = UserId
--   fieldLens UserId
--     = (Database.Persist.TH.lensPTH Database.Persist.Sqlite.entityKey)
--         (\ (Database.Persist.Sqlite.Entity _ value_a8yB) key_a8yC
--            -> (Database.Persist.Sqlite.Entity key_a8yC) value_a8yB)
--   fieldLens UserName
--     = (Database.Persist.TH.lensPTH
--          (userName . Database.Persist.Sqlite.entityVal))
--         (\ (Database.Persist.Sqlite.Entity key_a8yD value_a8yE) x_a8yF
--            -> (Database.Persist.Sqlite.Entity key_a8yD)
--                 value_a8yE {userName = x_a8yF})
--   fieldLens UserFriend
--     = (Database.Persist.TH.lensPTH
--          (userFriend . Database.Persist.Sqlite.entityVal))
--         (\ (Database.Persist.Sqlite.Entity key_a8yD value_a8yE) x_a8yF
--            -> (Database.Persist.Sqlite.Entity key_a8yD)
--                 value_a8yE {userFriend = x_a8yF})
--   fieldLens UserSSN
--     = (Database.Persist.TH.lensPTH
--          (userSSN . Database.Persist.Sqlite.entityVal))
--         (\ (Database.Persist.Sqlite.Entity key_a8yD value_a8yE) x_a8yF
--            -> (Database.Persist.Sqlite.Entity key_a8yD)
--                 value_a8yE {userSSN = x_a8yF})

{-@ userIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> _ _ @-}
userIdField :: EntityFieldWrapper User (Key User)
userIdField = EntityFieldWrapper UserId

{-@ userNameField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userName (entityVal row)}, {\field row -> field == userName (entityVal row)}> _ _ @-}
userNameField :: EntityFieldWrapper User String
userNameField = EntityFieldWrapper UserName

-- {-@ userFriendField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == userFriend (entityVal row)}, {\row field -> field == userFriend (entityVal row)}, {\field row -> field == userFriend (entityVal row)}> _ _ @-}
-- userFriendField :: EntityFieldWrapper User (Key User)
-- userFriendField = EntityFieldWrapper UserFriend

{-@ assume userSSNField :: EntityFieldWrapper <{\row viewer -> entityKey viewer == entityKey row}, {\row field -> field == userSSN (entityVal row)}, {\field row -> field == userSSN (entityVal row)}> _ {v:_ | len v == 9} @-}
userSSNField :: EntityFieldWrapper User String
userSSNField = EntityFieldWrapper UserSSN

-- ** TodoItem
{-@
data TodoItem = TodoItem
  { todoItemOwner :: Key User
  , todoItemTask :: {v:_ | len v > 0}
  }
@-}
-- data TodoItem = TodoItem
--   { todoItemOwner :: Key User
--   , todoItemTask :: String
--   } deriving (Eq, Show)

-- mkPersist sqlSettings [persistLowerCase|
-- TodoItem
--   owner UserId
--   task String
-- |]

-- instance PersistEntity TodoItem where
--   newtype Key TodoItem = TodoItemKey Int
--     deriving (PersistField, ToJSON, FromJSON, Show, Read, Eq, Ord)

--   data EntityField TodoItem typ where
--     TodoItemId :: EntityField TodoItem (Key TodoItem)
--     TodoItemOwner :: EntityField TodoItem (Key User)
--     TodoItemTask :: EntityField TodoItem String

--   data Unique TodoItem

--   keyToValues = undefined
--   keyFromValues = undefined
--   persistIdField = TodoItemId

{-@ todoItemIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> _ _ @-}
todoItemIdField :: EntityFieldWrapper TodoItem (Key TodoItem)
todoItemIdField = EntityFieldWrapper TodoItemId

{-@ todoItemOwnerField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == todoItemOwner (entityVal row)}, {\field row -> field == todoItemOwner (entityVal row)}> _ _ @-}
todoItemOwnerField :: EntityFieldWrapper TodoItem (Key User)
todoItemOwnerField = EntityFieldWrapper TodoItemOwner

{-@ assume todoItemTaskField :: EntityFieldWrapper <{\row viewer -> shared (todoItemOwner (entityVal row)) (entityKey viewer)}, {\row field -> field == todoItemTask (entityVal row)}, {\field row -> field == todoItemTask (entityVal row)}> _ {v:_ | len v > 0} @-}
todoItemTaskField :: EntityFieldWrapper TodoItem String
todoItemTaskField = EntityFieldWrapper TodoItemTask

-- ** Share
{-@
measure shared :: Key User -> Key User -> GHC.Types.Bool
@-}

{-@
data Share where
  Share :: Key User -> Key User -> {v: Share | shared (shareFrom v) (shareTo v)}
@-}
{-@ measure shareFrom @-}
{-@ measure shareTo @-}

{-@ invariant {v:Share | shared (shareFrom v) (shareTo v)} @-}


-- data Share = Share
--   { shareFrom :: Key User
--   , shareTo :: Key User
--   } deriving (Eq, Show)

-- instance PersistEntity Share where
--   newtype Key Share = ShareKey Int
--     deriving (PersistField, ToJSON, FromJSON, Show, Read, Eq, Ord)

--   data EntityField Share typ where
--     ShareId :: EntityField Share (Key Share)
--     ShareFrom :: EntityField Share (Key User)
--     ShareTo :: EntityField Share (Key User)

--   data Unique Share

--   keyToValues = undefined
--   keyFromValues = undefined
--   persistIdField = ShareId

{-@ assume shareIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == entityKey row}, {\field row -> field == entityKey row}> {v: Share | shared (shareFrom v) (shareTo v)} _ @-}
shareIdField :: EntityFieldWrapper Share (Key Share)
shareIdField = EntityFieldWrapper ShareId

{-@ assume shareFromField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareFrom (entityVal row)}, {\field row -> field == shareFrom (entityVal row)}> {v: Share | shared (shareFrom v) (shareTo v)} _ @-}
shareFromField :: EntityFieldWrapper Share (Key User)
shareFromField = EntityFieldWrapper ShareFrom

{-@ assume shareToField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == shareTo (entityVal row)}, {\field row -> field == shareTo (entityVal row)}> {v: Share | shared (shareFrom v) (shareTo v)} _ @-}
shareToField :: EntityFieldWrapper Share (Key User)
shareToField = EntityFieldWrapper ShareTo

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
