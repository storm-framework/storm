-- | Combinators and data types for Persistent-style filters.

module Filters where

import Database.Persist (PersistField)
import qualified Database.Persist as Persist

import Core
import Model

-- * Data types
{-@ data RefinedFilter record <r :: Entity record -> Bool, q :: Entity record -> Entity User -> Bool> = RefinedFilter _ @-}
data RefinedFilter record = RefinedFilter (Persist.Filter record)
{-@ data variance RefinedFilter covariant covariant contravariant @-}


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

-- * Combinators
{-@
(Filters.==.) ::
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
(EntityFieldWrapper field) ==. value = RefinedFilter (field Persist.==. value)

{-@
(Filters.<-.) ::
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
(EntityFieldWrapper field) <-. value = RefinedFilter (field Persist.<-. value)
