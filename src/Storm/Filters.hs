-- | Combinators and data types for Persistent-style filters.

module Storm.Filters where

import           Database.Persist               ( PersistField )
import qualified Database.Persist              as Persist

import           Storm.Core

-- * Data types
{-@
data Filter user record <
    q :: Entity record -> user -> Bool
  , r :: Entity record -> Bool
  > = Filter _
@-}
data Filter user record = Filter { toPersistFilters :: [Persist.Filter record] }
{-@ data variance Filter invariant covariant contravariant covariant @-}

{-@ assume trueF :: Filter<{\_ _ -> True}, {\_ -> True}> user record @-}
trueF :: Filter user record
trueF = Filter []

infixr 5 &&:
{-@ assume (&&:) ::
      forall < r  :: Entity record -> Bool,
               r1 :: Entity record -> Bool,
               r2 :: Entity record -> Bool,
               q  :: Entity record -> user -> Bool,
               q1 :: Entity record -> user -> Bool,
               q2 :: Entity record -> user -> Bool >.
               {row1 :: (Entity <r1> record), row2 :: (Entity <r2> record) |- {v:Entity record | v == row1 && v == row2} <: {v:(Entity <r> record) | True}}
             
               {row :: (Entity <r> record) |- {v:(user<q row>) | True} <: {v:(user<q1 row>) | True}}
               {row :: (Entity <r> record) |- {v:(user<q row>) | True} <: {v:(user<q2 row>) | True}}
             
               Filter<q1, r1> user record ->
               Filter<q2, r2> user record ->
               Filter<q, r> user record
@-}
(&&:) :: Filter user record -> Filter user record -> Filter user record
Filter f1 &&: Filter f2 = Filter (f1 ++ f2)

{-@
assume (||:) ::
  forall < r  :: Entity record -> Bool
         , r1 :: Entity record -> Bool
         , r2 :: Entity record -> Bool
         , q  :: Entity record -> user -> Bool
         , q1 :: Entity record -> user -> Bool
         , q2 :: Entity record -> user -> Bool
         >.
    {{v: Entity <r1> record | True} <: {v:(Entity <r> record) | True}}
    {{v: Entity <r2> record | True} <: {v:(Entity <r> record) | True}}
    {row :: (Entity <r> record) |- {v:(user<q row>) | True} <: {v:(user<q1 row>) | True}}
    {row :: (Entity <r> record) |- {v:(user<q row>) | True} <: {v:(user<q2 row>) | True}}
  
    Filter<q1, r1> user record ->
    Filter<q2, r2> user record ->
    Filter<q, r> user record
@-}
(||:) :: Filter user record -> Filter user record -> Filter user record
(Filter f1) ||: (Filter f2) = Filter $ f1 Persist.||. f2

-- * Combinators

{-@
(==.) ::
  forall < querypolicy :: Entity record -> user -> Bool
         , selector :: Entity record -> typ -> Bool
         , inverseselector :: typ -> Entity record -> Bool
         , fieldfilter :: typ -> Bool
         , filter :: Entity record -> Bool
         , r :: typ -> Bool
         , capability :: Entity record -> Bool
         , updatepolicy :: Entity record -> Entity record -> user -> Bool
         >.
    { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
    { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }
  
    EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> user record typ
    -> typ<r>
    -> Filter<querypolicy, filter> user record
@-}
(==.) :: PersistField typ => EntityFieldWrapper user record typ -> typ -> Filter user record
(EntityFieldWrapper field) ==. value = Filter [field Persist.==. value]

{-@
(!=.) ::
  forall < querypolicy :: Entity record -> user -> Bool
         , selector :: Entity record -> typ -> Bool
         , inverseselector :: typ -> Entity record -> Bool
         , fieldfilter :: typ -> Bool
         , filter :: Entity record -> Bool
         , r :: typ -> Bool
         , capability :: Entity record -> Bool
         , updatepolicy :: Entity record -> Entity record -> user -> Bool
         >.
    { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field != value} <: typ<fieldfilter> }
    { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} } 
      EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> user record typ
      -> typ<r>
      -> Filter<querypolicy, filter> user record
@-}
(!=.) :: PersistField typ => EntityFieldWrapper user record typ -> typ -> Filter user record
(EntityFieldWrapper field) !=. value = Filter [field Persist.!=. value]


{-@
(<.) ::
        forall < querypolicy :: Entity record -> user -> Bool
               , selector :: Entity record -> typ -> Bool
               , inverseselector :: typ -> Entity record -> Bool
               , capability :: Entity record -> Bool
               , updatepolicy :: Entity record -> Entity record -> user -> Bool
               >.
        
          EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> user record typ
          -> typ
          -> Filter<querypolicy, {\_ -> True}> user record
@-}
(<.) :: PersistField typ => EntityFieldWrapper user record typ -> typ -> Filter user record
(EntityFieldWrapper field) <. value = Filter [field Persist.<. value]

{-@
(>.) ::
        forall < querypolicy :: Entity record -> user -> Bool
               , selector :: Entity record -> typ -> Bool
               , inverseselector :: typ -> Entity record -> Bool
               , capability :: Entity record -> Bool
               , updatepolicy :: Entity record -> Entity record -> user -> Bool
               >.
        
          EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> user record typ
          -> typ
          -> Filter<querypolicy, {\_ -> True}> user record
@-}
(>.) :: PersistField typ => EntityFieldWrapper user record typ -> typ -> Filter user record
(EntityFieldWrapper field) >. value = Filter [field Persist.>. value]


{-@
(<-.) ::
        forall < querypolicy :: Entity record -> user -> Bool
               , selector :: Entity record -> typ -> Bool
               , inverseselector :: typ -> Entity record -> Bool
               , fieldfilter :: typ -> Bool
               , filter :: Entity record -> Bool
               , r :: typ -> Bool
               , capability :: Entity record -> Bool
               , updatepolicy :: Entity record -> Entity record -> user -> Bool
               >.
          { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldfilter> }
          { field :: typ<fieldfilter> |- {v:(Entity <inverseselector field> record) | True} <: {v:(Entity <filter> record) | True} }
        
          EntityFieldWrapper<querypolicy, selector, inverseselector, capability, updatepolicy> user record typ
          -> [typ<r>]
          -> Filter<querypolicy, filter> user record
@-}
(<-.) :: PersistField typ => EntityFieldWrapper user record typ -> [typ] -> Filter user record
(EntityFieldWrapper field) <-. value = Filter [field Persist.<-. value]


