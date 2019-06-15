{-# LANGUAGE GADTs, TypeFamilies #-}
{-@ LIQUID "--no-pattern-inline"                @-}
module Field where

-- * Models
class PersistEntity record where
  data Key record
  data EntityField record :: * -> *
  -- policy :: EntityField record typ -> Entity record -> Entity User -> Bool
  {-@ data variance EntityField covariant covariant contravariant @-}

{-@
data EntityFieldWrapper record typ <policy :: Entity record -> Entity User -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool> = EntityFieldWrapper _
@-}
data EntityFieldWrapper record typ = EntityFieldWrapper (EntityField record typ)
{-@ data variance EntityFieldWrapper covariant covariant contravariant invariant invariant @-}


{-@
data Entity record = Entity
  { entityKey :: _
  , entityVal :: _
  }
@-}
data Entity record = Entity
  { entityKey :: Key record
  , entityVal :: record
  }

-- ** User
{-@
data User = User
  { userId :: _
  , userName :: _
  , userFriend :: _
  , userSSN :: {v:_ | len v == 9}
  }
@-}
data User = User
  { userId :: Int
  , userName :: String
  , userFriend :: Int
  , userSSN :: String
  } deriving (Eq, Show)

instance PersistEntity User where
  data Key User = UserKey Int
    deriving (Eq, Show)

  {-@
  data EntityField User typ <policy :: Entity User -> Entity User -> Bool> where
    UserId :: EntityField <{\row viewer -> True}> _ _
  | UserName :: EntityField <{\row viewer -> userId (entityVal viewer) == userFriend (entityVal row)}> _ _
  | UserFriend :: EntityField <{\row viewer -> userId (entityVal viewer) == userFriend (entityVal row)}> _ _
  | UserSSN :: EntityField <{\row viewer -> userId (entityVal viewer) == userId (entityVal row)}> _ {v:_ | len v == 9}
  @-}
  data EntityField User typ where
    UserId :: EntityField User Int
    UserName :: EntityField User String
    UserFriend :: EntityField User Int
    UserSSN :: EntityField User String

{-@ userIdField :: EntityFieldWrapper <{\row viewer -> True}, {\row field -> field == userId (entityVal row)}, {\field row -> field == userId (entityVal row)}> _ _ @-}
userIdField :: EntityFieldWrapper User Int
userIdField = EntityFieldWrapper UserId

{-@ userNameField :: EntityFieldWrapper <{\row viewer -> userId (entityVal viewer) == userFriend (entityVal row)}, {\row field -> field == userName (entityVal row)}, {\field row -> field == userName (entityVal row)}> _ _ @-}
userNameField :: EntityFieldWrapper User String
userNameField = EntityFieldWrapper UserName

{-@ userFriendField :: EntityFieldWrapper <{\row viewer -> userId (entityVal viewer) == userFriend (entityVal row)}, {\row field -> field == userFriend (entityVal row)}, {\field row -> field == userFriend (entityVal row)}> _ _ @-}
userFriendField :: EntityFieldWrapper User Int
userFriendField = EntityFieldWrapper UserFriend

{-@ userSSNField :: EntityFieldWrapper <{\row viewer -> userId (entityVal viewer) == userId (entityVal row)}, {\row field -> field == userSSN (entityVal row)}, {\field row -> field == userSSN (entityVal row)}> _ {v:_ | len v == 9} @-}
userSSNField :: EntityFieldWrapper User String
userSSNField = EntityFieldWrapper UserSSN

-- * Infrastructure

{-@ data Tagged a <label :: Entity User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }

{-@ data variance Tagged covariant contravariant @-}

-- Placeholder for Data.Persistent's Filter type
data Filter a = Filter

{-@ data RefinedFilter record <r :: Entity record -> Bool, q :: Entity record -> Entity User -> Bool> = RefinedFilter (Filter record) @-}
data RefinedFilter record = RefinedFilter (Filter record)

{-@ data variance RefinedFilter covariant covariant contravariant @-}

{-@
(==.) ::
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
(==.) :: EntityFieldWrapper record typ -> typ -> RefinedFilter record
field ==. value = undefined

{-@
(<-.) ::
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
(<-.) :: EntityFieldWrapper record typ -> [typ] -> RefinedFilter record
field <-. value = undefined

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

{-@
selectList :: forall <q :: Entity record -> Entity User -> Bool, r :: Entity record -> Bool, p :: Entity User -> Bool>.
  {row :: (Entity <r> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True}}
  FilterList<q, r> record -> Tagged<p> [(Entity <r> record)]
@-}
selectList :: FilterList record -> Tagged [Entity record]
selectList x = undefined

{-@
project :: forall <r1 :: Entity record -> Bool, r2 :: typ -> Bool, policy :: Entity record -> Entity User -> Bool, p :: Entity User -> Bool, selector :: Entity record -> typ -> Bool>.
  { row :: (Entity <r1> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <policy row> User) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  [(Entity <r1> record)] ->
  EntityFieldWrapper<policy, selector> record typ ->
  Tagged<p> [typ<r2>]
@-}
project :: [Entity record] -> EntityFieldWrapper record typ -> Tagged [typ]
project = undefined

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure = Tagged
  -- f (a -> b) -> f a -> f b
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >>  t = t
  fail          = error

{-@ instance Monad Tagged where
     >>= :: forall <p :: Entity User -> Bool, f:: a -> b -> Bool>.
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>);
     >>  :: forall <p :: Entity User -> Bool>.
            x:Tagged<{\v -> false}> a
         -> Tagged<p> b
         -> Tagged<p> b;
     return :: a -> Tagged <{\v -> true}> a
  @-}

-- * Client code

{-@ combinatorExample1 :: RefinedFilter<{\row -> userName (entityVal row) == "alice"}, {\row v -> userId (entityVal v) == userFriend (entityVal row)}> User @-}
combinatorExample1 :: RefinedFilter User
combinatorExample1 = userNameField ==. "alice"

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = Empty

{-@ exampleList2 :: FilterList<{\_ v -> userId (entityVal v) == 1}, {\user -> userFriend (entityVal user) == 1}> User @-}
exampleList2 :: FilterList User
exampleList2 = (userFriendField ==. 1) ?: Empty

{-@ exampleList3 :: FilterList<{\_ v -> userId (entityVal v) == 1}, {\user -> userFriend (entityVal user) == 1 && userName (entityVal user) == "alice"}> User @-}
exampleList3 :: FilterList User
exampleList3 = userNameField ==. "alice" ?: userFriendField ==. 1 ?: Empty

{-@ exampleList4 :: FilterList<{\_ v -> userId (entityVal v) == 1}, {\user -> userFriend (entityVal user) == 1 && userName (entityVal user) == "alice"}> User @-}
exampleList4 :: FilterList User
exampleList4 = userFriendField ==. 1 ?: userNameField ==. "alice" ?: Empty

{-@ exampleList5 :: FilterList<{\row v -> userId (entityVal v) == userFriend (entityVal row)}, {\user -> userName (entityVal user) == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = userNameField ==. "alice" ?: Empty

{-@ exampleSelectList1 :: Tagged<{\v -> userId (entityVal v) == 1}> [{v : Entity User | userFriend (entityVal v) == 1}] @-}
exampleSelectList1 :: Tagged [Entity User]
exampleSelectList1 = selectList filters
  where
    {-@ filters :: FilterList<{\_ v -> userId (entityVal v) == 1}, {\v -> userFriend (entityVal v) == 1}> User @-}
    filters = userFriendField ==. 1 ?: Empty

{-@ exampleSelectList2 :: Tagged<{\v -> userId (entityVal v) == 1}> [{v : _ | userFriend (entityVal v) == 1 && userName (entityVal v) == "alice"}] @-}
exampleSelectList2 :: Tagged [Entity User]
exampleSelectList2 = selectList (userNameField ==. "alice" ?: userFriendField ==. 1 ?: Empty)

{-@ exampleSelectList3 :: Tagged<{\v -> False}> [{v : _ | userName (entityVal v) == "alice"}] @-}
exampleSelectList3 :: Tagged [Entity User]
exampleSelectList3 = selectList (userNameField ==. "alice" ?: Empty)

{-@ projectSelect1 :: [{v:_ | userFriend (entityVal v) == 1}] -> Tagged<{\_ -> False}> [{v:_ | len v == 9}] @-}
projectSelect1 :: [Entity User] -> Tagged [String]
projectSelect1 users = project users userSSNField

-- | This is fine: user 1 can see both the filtered rows and the name field in
--   each of these rows
{-@ names :: Tagged<{\v -> userId (entityVal v) == 1}> [String]
@-}
names :: Tagged [String]
names = do
  rows <- selectList (userFriendField ==. 1 ?: Empty)
  project rows userNameField

-- | This is bad: the result of the query is not public
{-@ bad1 :: Tagged<{\v -> True}> [{v: _ | userFriend (entityVal v) == 1}]
@-}
bad1 :: Tagged [Entity User]
bad1 = selectList (userFriendField ==. 1 ?: Empty)

-- | This is bad: who knows who else has name "alice" and is not friends with user 1?
{-@ bad2 :: Tagged<{\v -> userId (entityVal v) == 1}> [{v: _ | userName (entityVal v) == "alice"}]
@-}
bad2 :: Tagged [Entity User]
bad2 = selectList (userNameField ==. "alice" ?: Empty)

-- | This is bad: user 1 can see the filtered rows but not their SSNs
{-@ badSSNs :: Tagged<{\v -> userId (entityVal v) == 1}> [{v:_ | len v == 9}]
@-}
badSSNs :: Tagged [String]
badSSNs = do
  rows <- selectList (userFriendField ==. 1 ?: Empty)
  project rows userSSNField
