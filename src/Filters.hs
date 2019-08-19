-- | Combinators and data types for Persistent-style filters.

module Filters where

import Database.Persist (PersistField)
import qualified Database.Persist as Persist

import Core
import Model

-- * Data types
{-@
data Filter record <
    q :: Entity record -> Entity User -> Bool
  , r :: Entity record -> Bool
  > = Filter _
@-}
data Filter record = Filter (Persist.Filter record)
{-@ data variance Filter covariant contravariant covariant @-}

{-@
data FilterList record <
    q :: Entity record -> Entity User -> Bool
  , r :: Entity record -> Bool
> = FilterList _
@-}
data FilterList a = FilterList  { toPersistFilters :: [Persist.Filter a] }
{-@ data variance FilterList covariant contravariant covariant @-}

{-@ assume nilFL :: FilterList<{\_ _ -> True}, {\_ -> True}> record @-}
nilFL :: FilterList record
nilFL = FilterList []

infixr 5 ?:
{-@
assume (?:) :: forall <r :: Entity record -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool,
                q :: Entity record -> Entity User -> Bool, q1 :: Entity record -> Entity User -> Bool, q2 :: Entity record -> Entity User -> Bool>.
  {row1 :: (Entity <r1> record), row2 :: (Entity <r2> record) |- {v:Entity record | v == row1 && v == row2} <: {v:(Entity <r> record) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q1 row> User) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q2 row> User) | True}}
  Filter<q1, r1> record ->
  FilterList<q2, r2> record ->
  FilterList<q, r> record
@-}
(?:) :: Filter record -> FilterList record -> FilterList record
Filter f ?: FilterList fs = FilterList (f:fs)

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
  EntityFieldWrapper<policy, selector, inverseselector> record typ -> typ<r> -> Filter<policy, filter> record
@-}
(==.) :: PersistField typ => EntityFieldWrapper record typ -> typ -> Filter record
(EntityFieldWrapper field) ==. value = Filter (field Persist.==. value)

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
  EntityFieldWrapper<policy, selector, inverseselector> record typ -> [typ<r>] -> Filter<policy, filter> record
@-}
(<-.) :: PersistField typ => EntityFieldWrapper record typ -> [typ] -> Filter record
(EntityFieldWrapper field) <-. value = Filter (field Persist.<-. value)
