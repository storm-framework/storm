-- | Code that is common to all binah projects.
module BinahPrelude
  ( Tagged
  , FilterList(Empty), (?:)
  , selectList, projectList
  , module Model
  , module Filters
  ) where

import qualified Database.Persist
import Database.Persist hiding (Filter, selectList)
import Model
import Filters

{-@ data Tagged a <p :: Entity User -> Bool> = _ @-}
{-@ data variance Tagged covariant contravariant @-}
data Tagged a = Tagged { content :: a }
  deriving Eq

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure = Tagged
  (Tagged f) <*> (Tagged x) = Tagged (f x)

{-@
instance Monad Tagged where
  >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>.
    x:Tagged <p> a ->
    (u:a -> Tagged <p> (b <f u>)) ->
    Tagged <p> (b<f (content x)>);
  >> :: forall <p :: User -> Bool>.
    x:Tagged<{\v -> False}> a ->
    Tagged<p> b ->
    Tagged<p> b;
  return :: a -> Tagged <{\v -> True}> a
@-}
instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >> t = t
  fail = error

{-@
data FilterList record <q :: Entity record -> User -> Bool, r :: Entity record -> Bool> where
  Empty :: FilterList<{\_ _ -> True}, {\_ -> True}> record;
  Cons :: Filter<{\_ -> True}, {\_ _ -> False}> record ->
    FilterList<{\_ _ -> False}, {\_ -> True}> record ->
    FilterList<q, r> record
@-}
{-@ data variance FilterList covariant contravariant covariant @-}
data FilterList a = Empty | Cons (Filter a) (FilterList a)

{-@
(?:) :: forall <r :: Entity record -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool,
                q :: Entity record -> Entity User -> Bool, q1 :: Entity record -> Entity User -> Bool, q2 :: Entity record -> Entity User -> Bool>.
  {vr1 :: (Entity record)<r1>, vr2 :: (Entity record)<r2> |- {v:Entity record | v == vr1 && v == vr2} <: (Entity record)<r>}
  {row :: (Entity record)<r> |- (Entity User)<q row> <: (Entity User)<q1 row>}
  {row :: (Entity record)<r> |- (Entity User)<q row> <: (Entity User)<q2 row>}
  Filter<r1, q1> record ->
  FilterList<q2, r2> record ->
  FilterList<q, r> record
@-}
(?:) :: Filter record -> FilterList record -> FilterList record
f ?: fs = f `Cons` fs

infixr 5 ?:

{-@
selectList :: forall <q :: Entity a -> Entity User -> Bool, r :: Entity a -> Bool, p :: Entity User -> Bool>.
  {row :: (Entity a)<r> |- (Entity User)<p> <: (Entity User)<q row>}
  FilterList<q, r> a -> Tagged<p> [(Entity a)<r>]
@-}
selectList :: FilterList a -> Tagged [Entity a]
selectList = undefined

{-@
assume projectList :: forall <r :: record -> Bool, q :: record -> User -> Bool, p :: User -> Bool>.
  {row :: record<r> |- User<p> <: User<q row>}
  [record<r>] ->
  EntityField<q> record field ->
  Tagged<p> [field]
@-}
projectList :: Projectable record => [Database.Persist.Entity record] -> EntityField record field -> Tagged [field]
projectList as field = return (project field <$> as)
