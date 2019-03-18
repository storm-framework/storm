{-# LANGUAGE GADTs #-}
{-@ LIQUID "--no-pattern-inline"                @-}
module Field where

import qualified Database.Persist

{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }
  deriving Eq

{-@ data variance Tagged covariant contravariant @-}

-- Placeholder for Data.Persistent's Filter type
data Filter a = Filter

{-@ data RefinedFilter record <r :: record -> Bool, q :: record -> User -> Bool> = RefinedFilter (Filter record) @-}
data RefinedFilter record = RefinedFilter (Filter record)

{-@ data variance RefinedFilter covariant covariant contravariant @-}

{-@
data User = User
     { userId   :: Int,
       userName :: String
     , userFriend :: Int
     , userSSN    :: Int
     }
@-}
data User = User { userId::Int, userName :: String, userFriend :: Int, userSSN :: Int }
    deriving (Eq, Show)

{-@
data EntityField record typ <q :: record -> User -> Bool> where 
   Field.UserName :: EntityField <{\row v -> userId v = userFriend row}> User {v:_ | True}
 | Field.UserFriend :: EntityField <{\row v -> userId v = userFriend row}> User {v:_ | True}
 | Field.UserSSN :: EntityField <{\row v -> userId v = userId row}> User {v:_ | True}
@-}
{-@ data variance EntityField covariant covariant contravariant @-}
data EntityField a b where
  UserName :: EntityField User String
  UserFriend :: EntityField User Int
  UserSSN :: EntityField User Int

{-@ filterUserName ::
       val: String -> RefinedFilter<{\row -> userName row == val}, {\row v -> userId v = userFriend row}> User @-}
filterUserName :: String -> RefinedFilter User
filterUserName val = RefinedFilter Filter


{-@ filterUserSSN ::
       val: Int -> RefinedFilter<{\row -> userSSN row == val}, {\row v -> userId v = userId row}> User @-}
filterUserSSN :: Int -> RefinedFilter User
filterUserSSN val = RefinedFilter Filter


{-@ filterUserFriend ::
       val: Int -> RefinedFilter<{\row ->userFriend row == val}, {\row v -> userId v = userFriend row}> User @-}
filterUserFriend :: Int -> RefinedFilter User
filterUserFriend val = RefinedFilter Filter

{-@
data FilterList a <q :: a -> User -> Bool, r :: a -> Bool> where
    Empty :: FilterList<{\_ _ -> True}, {\_ -> True}> a
  | Cons :: RefinedFilter<{\_ -> True}, {\_ _ -> False}> a ->
            FilterList<{\_ _ -> False}, {\_ -> True}> a ->
            FilterList<q, r> a
@-}
{-@ data variance FilterList covariant contravariant covariant @-}
data FilterList a = Empty | Cons (RefinedFilter a) (FilterList a)

-- Don't use `Cons` to construct FilterLists: only ever use `?:`. This should be
-- enforced by not exporting `Cons`.

infixr 5 ?:
{-@
(?:) :: forall <r :: a -> Bool, r1 :: a -> Bool, r2 :: a -> Bool,
                q :: a -> User -> Bool, q1 :: a -> User -> Bool, q2 :: a -> User -> Bool>.
  {a_r1 :: a<r1>, a_r2 :: a<r2> |- {v:a | v == a_r1 && v == a_r2} <: a<r>}
  {row :: a<r> |- User<q row> <: User<q1 row>}
  {row :: a<r> |- User<q row> <: User<q2 row>}
  RefinedFilter<r1, q1> a ->
  FilterList<q2, r2> a ->
  FilterList<q, r> a
@-}
(?:) :: RefinedFilter a -> FilterList a -> FilterList a
f ?: fs = f `Cons` fs

{-@
selectList :: forall <q :: a -> User -> Bool, r :: a -> Bool, p :: User -> Bool>.
  {row :: a<r> |- User<p> <: User<q row>}
  FilterList<q, r> a -> Tagged<p> [a<r>]
@-}
selectList :: FilterList a -> Tagged [a]
selectList = undefined

{-@ assume projectUser :: forall <r :: User -> Bool, q :: User -> User -> Bool, p :: User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q row> }
                         [User<r>] -> f: EntityField<q> User typ
                         -> Tagged<p> [typ]
@-}
projectUser ::
      [User]
      -> EntityField User typ
      -> Tagged [typ]
projectUser = undefined

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
  -- f (a -> b) -> f a -> f b
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >>  t = t
  fail          = error

{-@ instance Monad Tagged where
     >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>.
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>);
     >>  :: forall <p :: User -> Bool>.
            x:Tagged<{\v -> false}> a
         -> Tagged<p> b
         -> Tagged<p> b;
     return :: a -> Tagged <{\v -> true}> a
  @-}

{- Client code -}

{-@ exampleList1 :: FilterList<{\_ -> True}, {\_ -> True}> User @-}
exampleList1 :: FilterList User
exampleList1 = Empty

{-@ exampleList2 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1}> User @-}
exampleList2 :: FilterList User
exampleList2 = filterUserFriend 1 ?: Empty

{-@ exampleList3 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1 && userName user == "alice"}> User @-}
exampleList3 :: FilterList User
exampleList3 = filterUserName "alice" ?: filterUserFriend 1 ?: Empty

{-@ exampleList4 :: FilterList<{\_ v -> userId v == 1}, {\user -> userFriend user == 1 && userName user == "alice"}> User @-}
exampleList4 :: FilterList User
exampleList4 = filterUserFriend 1 ?: filterUserName "alice" ?: Empty

{-@ exampleList5 :: FilterList<{\row v -> userId v == userFriend row}, {\user -> userName user == "alice"}> User @-}
exampleList5 :: FilterList User
exampleList5 = filterUserName "alice" ?: Empty

{-@ exampleSelectList1 :: Tagged<{\v -> userId v == 1}> [{v : User | userFriend v == 1}] @-}
exampleSelectList1 :: Tagged [User]
exampleSelectList1 = selectList (filterUserFriend 1 ?: Empty)

{-@ exampleSelectList2 :: Tagged<{\v -> userId v == 1}> [{v : User | userFriend v == 1 && userName v == "alice"}] @-}
exampleSelectList2 :: Tagged [User]
exampleSelectList2 = selectList (filterUserName "alice" ?: filterUserFriend 1 ?: Empty)

{-@ exampleSelectList3 :: Tagged<{\v -> False}> [{v : User | userName v == "alice"}] @-}
exampleSelectList3 :: Tagged [User]
exampleSelectList3 = selectList (filterUserName "alice" ?: Empty)

-- | This is fine: user 1 can see both the filtered rows and the name field in
--   each of these rows
{-@ names :: Tagged<{\v -> userId v == 1}> [String]
@-}
names :: Tagged [String]
names = do
  rows <- selectList (filterUserFriend 1 ?: Empty)
  projectUser rows UserName

-- | This is bad: the result of the query is not public
{-@ bad1 :: Tagged<{\v -> true}> [{v: User | userFriend v == 1}]
@-}
bad1 :: Tagged [User]
bad1 = selectList (filterUserFriend 1 ?: Empty)

-- | This is bad: who knows who else has name "alice" and is not friends with user 1?
{-@ bad2 :: Tagged<{\v -> userId v == 1}> [{v: User | userName v == "alice"}]
@-}
bad2 :: Tagged [User]
bad2 = selectList (filterUserName "alice" ?: Empty)

-- | This is bad: user 1 can see the filtered rows but not their SSNs
{-@ badSSNs :: Tagged<{\v -> userId v == 1}> [Int]
@-}
badSSNs :: Tagged [Int]
badSSNs = do
  rows <- selectList (filterUserFriend 1 ?: Empty)
  projectUser rows UserSSN
