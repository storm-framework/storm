{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{- LIQUID "--exact-data-con"                      @-}
{- LIQUID "--higherorder"                         @-}
{- LIQUID "--no-termination"                      @-}
{- LIQUID "--no-totality"                      @-}
{-@ LIQUID "--no-pattern-inline"                @-}
-- {-@ LIQUID "--ple" @-} 


module Field
where

import Prelude hiding (sequence, mapM, filter)
import qualified Data.Set as Set


{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }
  deriving Eq

{-@ data variance Tagged covariant contravariant @-}

data RefinedPersistFilter = EQUAL

-- | r is the postcondition of the filter (a property of each row)
--   q is the policy of the filter per row
{-@ data RefinedFilter record typ <r :: record -> Bool, q :: record -> User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField<q> record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 
  @-}
{-@ data variance RefinedFilter covariant covariant covariant contravariant @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }    
    
{-@
data User = User
     { userName :: String
     , userFriend :: User
     , userSSN    :: Int
     }
@-}
data User = User { userName :: String, userFriend :: User, userSSN :: Int }
    deriving (Eq, Show)

{-@
data EntityField record typ <q :: record -> User -> Bool> where 
   Field.UserName :: EntityField <{\row v -> v = userFriend row}> User {v:_ | True}
 | Field.UserFriend :: EntityField <{\row v -> v = userFriend row}> User {v:_ | True}
 | Field.UserSSN :: EntityField <{\row v -> v = row}> User {v:_ | True}
@-}
{-@ data variance EntityField covariant covariant contravariant @-}
data EntityField a b where
  UserName :: EntityField User String
  UserFriend :: EntityField User User
  UserSSN :: EntityField User Int

{-@ filterUserName ::
       val: String -> RefinedFilter<{\row -> userName row == val}, {\row v -> v = userFriend row}> User String @-}
filterUserName :: String -> RefinedFilter User String 
filterUserName val = RefinedFilter UserName val EQUAL


{-@ filterUserSSN ::
       val: Int -> RefinedFilter<{\row -> userSSN row == val}, {\row v -> v = row}> User Int @-}
filterUserSSN :: Int -> RefinedFilter User Int 
filterUserSSN val = RefinedFilter UserSSN val EQUAL


{-@ filterUserFriend ::
       val: User -> RefinedFilter<{\row -> userFriend row == val}, {\row v -> v = userFriend row}> User User @-}
filterUserFriend :: User -> RefinedFilter User User 
filterUserFriend val = RefinedFilter UserFriend val EQUAL

       
-- | r is the postcondition of the filter,
--   p is the policy of the result
--   q is the per-row policy
{-@ assume selectUser :: forall <r1 :: User -> Bool, r :: User -> Bool, q :: User -> User -> Bool, p :: User -> Bool>.
                         { row :: User<r1> |- User<p> <: User<q row> }
                         { User<r> <: User<r1> }
                         f: (RefinedFilter<r1, q> User typ) -> Tagged<p> [User<r>]
@-}
selectUser ::
      RefinedFilter User typ
      -> Tagged [User]
selectUser fs = undefined


-- | r is the postcondition of the filter,
--   p is the policy of the result
--   q is the per-row policy
{-@ assume selectUserOrig :: forall <r :: User -> Bool, q :: User -> User -> Bool, p :: User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q row> }
                         f: (RefinedFilter<r, q> User typ) -> Tagged<p> [User<r>]
@-}
selectUserOrig ::
      RefinedFilter User typ
      -> Tagged [User]
selectUserOrig fs = undefined

-- | r is the postcondition of the filter,
--   p is the policy of the result
--   q is the per-row policy
{-@ assume selectUser2 :: forall <r1 :: User -> Bool, q1 :: User -> User -> Bool,
                                  r2 :: User -> Bool, q2 :: User -> User -> Bool, p :: User -> Bool,
                                  r  :: User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q1 row> }
                         { row :: User<r> |- User<p> <: User<q2 row> }
                         { User<r> <: User<r1> }
                         { User<r> <: User<r2> }
                         f: (RefinedFilter<r1, q1> User typ) ->
                         g: (RefinedFilter<r2, q2> User typ2) -> Tagged<p> [User<r>]
@-}
selectUser2 ::
      RefinedFilter User typ
      -> RefinedFilter User typ2
      -> Tagged [User]
selectUser2 fs fs' = undefined

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

{-@ reflect aliceName @-}
aliceName :: String
aliceName = ['a', 'l', 'i', 'c', 'e']

{-@ reflect alice @-}
alice :: User
alice = User aliceName alice 1

{-@ reflect aliceSSN@-}
aliceSSN :: Int
aliceSSN = 1

-- | This is fine: policy on friends is self-referential,
-- so alice can see all users who are friends with her
{-@ good :: Tagged<{\v -> v == alice}> [{v: User | userFriend v == alice}]
@-}
good :: Tagged [User]
good = selectUser (filterUserFriend alice)

-- -- | This is fine: policy on friends is self-referential,
-- -- so alice can see all users who are friends with her
{-@ goodtest :: a:User->Tagged<{\v -> v == alice}> [{v: User | v==alice}]
@-}
goodtest :: User -> Tagged [User]
goodtest a = selectUser2 (filterUserName aliceName) (filterUserSSN aliceSSN )

-- -- | This is fine: policy on friends is self-referential,
-- -- so alice can see all users who are friends with her
-- {-@ goodshouldbe :: Tagged<{\v -> v == alice}> [{v: User | userName v == aliceName}]
-- @-}
-- goodshouldbe :: Tagged [User]
-- goodshouldbe = selectUser (filterUserName aliceName)

-- {-@ goodshouldbe1 :: Tagged<{\v -> v == alice}> [User]
-- @-}
-- goodshouldbe1 :: Tagged [User]
-- goodshouldbe1 = selectUserOrig (filterUserSSN aliceSSN)


-- | This is fine: alice can see both the filtered rows
-- and the name field in each of these rows
{-@ names :: Tagged<{\v -> v == alice}> [String]
@-}
names :: Tagged [String]
names = do
  rows <- selectUser (filterUserFriend alice)
  projectUser rows UserName

{-
-- | This is bad: the result of the query is not public
{-@ bad1 :: Tagged<{\v -> true}> [{v: User | userFriend v == alice}]
@-}
bad1 :: Tagged [User]
bad1 = selectUser (filterUserFriend alice)

-- | This is bad: who knows who else has name "alice" and is not friends with our alice?
{-@ bad2 :: Tagged<{\v -> v == alice}> [{v: User | userName v == aliceName}]
@-}
bad2 :: Tagged [User]
bad2 = selectUser (filterUserName aliceName)

-- | This is bad: alice can see the filtered rows
-- but not their SSNs
{-@ badSSNs :: Tagged<{\v -> v == alice}> [Int]
@-}
badSSNs :: Tagged [Int]
badSSNs = do
  rows <- selectUser (filterUserFriend alice)
  projectUser rows UserSSN
  -}
{-@ mySSN :: Tagged<{\v -> v == alice}> [Int]
@-}  
mySSN :: Tagged [Int]
mySSN = projectUser [alice] UserSSN
  



