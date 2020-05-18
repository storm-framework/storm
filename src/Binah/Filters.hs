-- | Combinators and data types for Persistent-style filters.

module Binah.Filters where

import           Database.Persist               ( PersistField )
import qualified Database.Persist              as Persist

import           Binah.Core
import           Model

-- * Data types
{-@
data Filter record <
    q :: Entity record -> Entity User -> Bool
  , r :: Entity record -> Bool
  > = Filter _
@-}
data Filter record = Filter { toPersistFilters :: [Persist.Filter record] }
{-@ data variance Filter covariant contravariant covariant @-}

{-@ assume trueF :: Filter<{\_ _ -> True}, {\_ -> True}> record @-}
trueF :: Filter record
trueF = Filter []

infixr 5 &&:
{-@
assume (&&:) ::
forall < r  :: Entity record -> Bool
       , r1 :: Entity record -> Bool
       , r2 :: Entity record -> Bool
       , q  :: Entity record -> Entity User -> Bool
       , q1 :: Entity record -> Entity User -> Bool
       , q2 :: Entity record -> Entity User -> Bool
       >.
  {row1 :: (Entity <r1> record), row2 :: (Entity <r2> record) |- {v:Entity record | v == row1 && v == row2} <: {v:(Entity <r> record) | True}}

  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q1 row> User) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q2 row> User) | True}}

  Filter<q1, r1> record ->
  Filter<q2, r2> record ->
  Filter<q, r> record
@-}
(&&:) :: Filter record -> Filter record -> Filter record
Filter f1 &&: Filter f2 = Filter (f1 ++ f2)

{-@
assume (||:) ::
forall < r  :: Entity record -> Bool
       , r1 :: Entity record -> Bool
       , r2 :: Entity record -> Bool
       , q  :: Entity record -> Entity User -> Bool
       , q1 :: Entity record -> Entity User -> Bool
       , q2 :: Entity record -> Entity User -> Bool
       >.
  {{v: Entity <r1> record | True} <: {v:(Entity <r> record) | True}}
  {{v: Entity <r2> record | True} <: {v:(Entity <r> record) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q1 row> User) | True}}
  {row :: (Entity <r> record) |- {v:(Entity <q row> User) | True} <: {v:(Entity <q2 row> User) | True}}

  Filter<q1, r1> record ->
  Filter<q2, r2> record ->
  Filter<q, r> record
@-}
(||:) :: Filter record -> Filter record -> Filter record
(Filter f1) ||: (Filter f2) = Filter $ f1 Persist.||. f2

-- * Combinators

{-@
(==.) ::
forall < querypolicy :: Entity record -> Entity User -> Bool
       , selector :: Entity record -> typ -> Bool
       , inverseselector :: typ -> Entity record -> Bool
       , fieldfilter :: typ -> Bool
       , filter :: Entity record -> Bool
       , r :: typ -> Bool
       , capability :: Entity record -> Bool
       , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
       >.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
  { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }

  EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> record typ 
  -> typ<r>
  -> Filter<querypolicy, filter> record
@-}
(==.) :: PersistField typ => EntityFieldWrapper record typ -> typ -> Filter record
(EntityFieldWrapper field) ==. value = Filter [field Persist.==. value]

{-@
(!=.) ::
forall < querypolicy :: Entity record -> Entity User -> Bool
       , selector :: Entity record -> typ -> Bool
       , inverseselector :: typ -> Entity record -> Bool
       , fieldfilter :: typ -> Bool
       , filter :: Entity record -> Bool
       , r :: typ -> Bool
       , capability :: Entity record -> Bool
       , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
       >.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field != value} <: typ<fieldfilter> }
  { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }

  EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> record typ 
  -> typ<r>
  -> Filter<querypolicy, filter> record
@-}
(!=.) :: PersistField typ => EntityFieldWrapper record typ -> typ -> Filter record
(EntityFieldWrapper field) !=. value = Filter [field Persist.!=. value]

{-@
(<-.) ::
forall < querypolicy :: Entity record -> Entity User -> Bool
       , selector :: Entity record -> typ -> Bool
       , inverseselector :: typ -> Entity record -> Bool
       , fieldfilter :: typ -> Bool
       , filter :: Entity record -> Bool
       , r :: typ -> Bool
       , capability :: Entity record -> Bool
       , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
       >.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
  { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }

  EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> record typ 
  -> [typ<r>] 
  -> Filter<querypolicy, filter> record
@-}
(<-.) :: PersistField typ => EntityFieldWrapper record typ -> [typ] -> Filter record
(EntityFieldWrapper field) <-. value = Filter [field Persist.<-. value]
