{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-@ LIQUID "--no-pattern-inline" @-}

module Binah.Helpers where

import           Control.Monad.Reader           ( MonadReader(..) )
import           Data.Text                      ( Text
                                                , pack
                                                )
import           Database.Persist.Sql           ( fromSqlKey
                                                , ToBackendKey
                                                , SqlBackend
                                                )
import           Database.Persist               ( PersistEntity )
import qualified Database.Persist              as DB
import           Binah.Frankie

import           Binah.Actions
import           Binah.Core
import           Binah.Infrastructure
import           Binah.Filters
import           Model


{-@
assume project2 :: forall < policy1 :: Entity record -> Entity User -> Bool
                          , policy2 :: Entity record -> Entity User -> Bool
                          , selector1 :: Entity record -> typ1 -> Bool
                          , selector2 :: Entity record -> typ2 -> Bool
                          , flippedselector1 :: typ1 -> Entity record -> Bool
                          , flippedselector2 :: typ2 -> Entity record -> Bool
                          , p :: Entity record -> Bool
                          , label :: Entity User -> Bool
                          >.
  {row :: (Entity<p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy1 row> User) | True}}
  {row :: (Entity<p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy2 row> User) | True}}

  ( EntityFieldWrapper<policy1, selector1, flippedselector1> record typ1
  , EntityFieldWrapper<policy2, selector2, flippedselector2> record typ2
  ) ->
  row:(Entity<p> record) ->
  TaggedT<label, {\_ -> False}> _ (typ1<selector1 row>, typ2<selector2 row>)
@-}
project2
    :: (Monad m, PersistEntity record)
    => (EntityFieldWrapper record typ1, EntityFieldWrapper record typ2)
    -> Entity record
    -> TaggedT m (typ1, typ2)
project2 (field1, field2) record = do
    field1 <- project field1 record
    field2 <- project field2 record
    return (field1, field2)


{-@
assume project3 :: forall < policy1 :: Entity record -> Entity User -> Bool
                          , policy2 :: Entity record -> Entity User -> Bool
                          , policy3 :: Entity record -> Entity User -> Bool
                          , selector1 :: Entity record -> typ1 -> Bool
                          , selector2 :: Entity record -> typ2 -> Bool
                          , selector3 :: Entity record -> typ3 -> Bool
                          , flippedselector1 :: typ1 -> Entity record -> Bool
                          , flippedselector2 :: typ2 -> Entity record -> Bool
                          , flippedselector3 :: typ3 -> Entity record -> Bool
                          , p :: Entity record -> Bool
                          , label :: Entity User -> Bool
                          >.
  {row :: (Entity<p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy1 row> User) | True}}
  {row :: (Entity<p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy2 row> User) | True}}
  {row :: (Entity<p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy3 row> User) | True}}

  ( EntityFieldWrapper<policy1, selector1, flippedselector1> record typ1
  , EntityFieldWrapper<policy2, selector2, flippedselector2> record typ2
  , EntityFieldWrapper<policy3, selector3, flippedselector3> record typ3
  ) ->
  row:(Entity<p> record) ->
  TaggedT<label, {\_ -> False}> _ (typ1<selector1 row>, typ2<selector2 row>, typ3<selector3 row>)
@-}
project3
    :: (Monad m, PersistEntity record)
    => ( EntityFieldWrapper record typ1
       , EntityFieldWrapper record typ2
       , EntityFieldWrapper record typ3
       )
    -> Entity record
    -> TaggedT m (typ1, typ2, typ3)
project3 (field1, field2, field3) record = do
    field1 <- project field1 record
    field2 <- project field2 record
    field3 <- project field3 record
    return (field1, field2, field3)


{-@
assume projectList2 :: forall < policy1 :: Entity record -> Entity User -> Bool
                              , policy2 :: Entity record -> Entity User -> Bool
                              , selector1 :: Entity record -> typ1 -> Bool
                              , selector2 :: Entity record -> typ2 -> Bool
                              , inverseselector1 :: typ1 -> Entity record -> Bool
                              , inverseselector2 :: typ2 -> Entity record -> Bool
                              , q1 :: typ1 -> Bool
                              , q2 :: typ2 -> Bool
                              , q3 :: typ3 -> Bool
                              , p :: Entity record -> Bool
                              , label :: Entity User -> Bool
                              >.
  { row :: (Entity <p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity <policy1 row> User) | True} }
  { row :: (Entity <p> record) |- typ1<selector1 row> <: typ1<q1> }

  { row :: (Entity <p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity <policy2 row> User) | True} }
  { row :: (Entity <p> record) |- typ2<selector2 row> <: typ2<q2> }

  ( EntityFieldWrapper<policy1, selector1, inverseselector1> record typ1
  , EntityFieldWrapper<policy2, selector2, inverseselector2> record typ2
  ) ->
  [(Entity <p> record)] ->
  TaggedT<label, {\_ -> False}> _ [(typ1<q1>, typ2<q2>)]
@-}
projectList2
    :: (Monad m, PersistEntity record)
    => (EntityFieldWrapper record typ1, EntityFieldWrapper record typ2)
    -> [Entity record]
    -> TaggedT m [(typ1, typ2)]
projectList2 (field1, field2) records = do
    fields1 <- projectList field1 records
    fields2 <- projectList field2 records
    return $ zip fields1 fields2

{-@
assume projectList3 :: forall < policy1 :: Entity record -> Entity User -> Bool
                              , policy2 :: Entity record -> Entity User -> Bool
                              , policy3 :: Entity record -> Entity User -> Bool
                              , selector1 :: Entity record -> typ1 -> Bool
                              , selector2 :: Entity record -> typ2 -> Bool
                              , selector3 :: Entity record -> typ3 -> Bool
                              , inverseselector1 :: typ1 -> Entity record -> Bool
                              , inverseselector2 :: typ2 -> Entity record -> Bool
                              , inverseselector3 :: typ3 -> Entity record -> Bool
                              , q1 :: typ1 -> Bool
                              , q2 :: typ2 -> Bool
                              , q3 :: typ3 -> Bool
                              , p :: Entity record -> Bool
                              , label :: Entity User -> Bool
                              >.
  { row :: (Entity <p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity <policy1 row> User) | True} }
  { row :: (Entity <p> record) |- typ1<selector1 row> <: typ1<q1> }

  { row :: (Entity <p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity <policy2 row> User) | True} }
  { row :: (Entity <p> record) |- typ2<selector2 row> <: typ2<q2> }

  { row :: (Entity <p> record) |- {v:(Entity <label> User) | True} <: {v:(Entity <policy3 row> User) | True} }
  { row :: (Entity <p> record) |- typ3<selector3 row> <: typ3<q3> }

  ( EntityFieldWrapper<policy1, selector1, inverseselector1> record typ1
  , EntityFieldWrapper<policy2, selector2, inverseselector2> record typ2
  , EntityFieldWrapper<policy3, selector3, inverseselector3> record typ3
  ) ->
  [(Entity <p> record)] ->
  TaggedT<label, {\_ -> False}> _ [(typ1<q1>, typ2<q2>, typ3<q3>)]
@-}
projectList3
    :: (Monad m, PersistEntity record)
    => ( EntityFieldWrapper record typ1
       , EntityFieldWrapper record typ2
       , EntityFieldWrapper record typ3
       )
    -> [Entity record]
    -> TaggedT m [(typ1, typ2, typ3)]
projectList3 (field1, field2, field3) records = do
    fields1 <- projectList field1 records
    fields2 <- projectList field2 records
    fields3 <- projectList field3 records
    return $ zip3 fields1 fields2 fields3


{-@
assume selectFirstOr404 :: forall < q  :: Entity record -> Entity User -> Bool
                                  , r1 :: Entity record -> Bool
                                  , r2 :: Entity record -> Bool
                                  , p :: Entity User -> Bool>.
  { row :: record
    |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }

  { row :: (Entity <r2> record)
    |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True}
  }
  Filter<q, r1> record -> TaggedT<p, {\v -> v == currentUser}> _ (Entity <r2> record)
@-}
selectFirstOr404
    :: ( DB.PersistQueryRead backend
       , DB.PersistRecordBackend record backend
       , MonadReader backend m
       , MonadController w m
       , MonadTIO m
       )
    => Filter record
    -> TaggedT m (Entity record)
selectFirstOr404 = selectFirstOr notFound

{-@
assume selectFirstOr :: forall < q  :: Entity record -> Entity User -> Bool
                               , r1 :: Entity record -> Bool
                               , r2 :: Entity record -> Bool
                               , p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  _ -> Filter<q, r1> record -> TaggedT<p, {\v -> v == currentUser}> _ (Entity <r2> record)
@-}
selectFirstOr
    :: ( DB.PersistQueryRead backend
       , DB.PersistRecordBackend record backend
       , MonadReader backend m
       , MonadController w m
       , MonadTIO m
       )
    => Response
    -> Filter record
    -> TaggedT m (Entity record)
selectFirstOr response filters = do
    maybeRecord <- selectFirst filters
    case maybeRecord of
        Just record -> return record
        Nothing     -> respondTagged response
