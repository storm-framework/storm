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
import           Frankie.Log

import           Binah.Actions
import           Binah.Core
import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Insert

{-@
project2 :: forall < policy1 :: Entity record -> user -> Bool
                   , policy2 :: Entity record -> user -> Bool
                   , selector1 :: Entity record -> typ1 -> Bool
                   , selector2 :: Entity record -> typ2 -> Bool
                   , flippedselector1 :: typ1 -> Entity record -> Bool
                   , flippedselector2 :: typ2 -> Entity record -> Bool
                   , p :: Entity record -> Bool
                   , label :: user -> Bool
                   >.
  {row :: (Entity<p> record) |- {v:(user<label>) | True} <: {v:(user<policy1 row>) | True}}
  {row :: (Entity<p> record) |- {v:(user<label>) | True} <: {v:(user<policy2 row>) | True}}

  ( EntityFieldWrapper<policy1, selector1, flippedselector1> user record typ1
  , EntityFieldWrapper<policy2, selector2, flippedselector2> user record typ2
  )
  -> row:(Entity<p> record)
  -> TaggedT<label, {\_ -> False}> user m (typ1<selector1 row>, typ2<selector2 row>)
@-}
project2
    :: (Monad m, PersistEntity record)
    => (EntityFieldWrapper user record typ1, EntityFieldWrapper user record typ2)
    -> Entity record
    -> TaggedT user m (typ1, typ2)
project2 (field1, field2) record = do
    field1 <- project field1 record
    field2 <- project field2 record
    return (field1, field2)

{-@
project3 :: forall < policy1 :: Entity record -> user -> Bool
                   , policy2 :: Entity record -> user -> Bool
                   , policy3 :: Entity record -> user -> Bool
                   , selector1 :: Entity record -> typ1 -> Bool
                   , selector2 :: Entity record -> typ2 -> Bool
                   , selector3 :: Entity record -> typ3 -> Bool
                   , flippedselector1 :: typ1 -> Entity record -> Bool
                   , flippedselector2 :: typ2 -> Entity record -> Bool
                   , flippedselector3 :: typ3 -> Entity record -> Bool
                   , p :: Entity record -> Bool
                   , label :: user -> Bool
                   >.
  {row :: (Entity<p> record) |- {v:(user<label>) | True} <: {v:(user<policy1 row>) | True}}
  {row :: (Entity<p> record) |- {v:(user<label>) | True} <: {v:(user<policy2 row>) | True}}
  {row :: (Entity<p> record) |- {v:(user<label>) | True} <: {v:(user<policy3 row>) | True}}

  ( EntityFieldWrapper<policy1, selector1, flippedselector1> user record typ1
  , EntityFieldWrapper<policy2, selector2, flippedselector2> user record typ2
  , EntityFieldWrapper<policy3, selector3, flippedselector3> user record typ3
  )
  -> row:(Entity<p> record)
  -> TaggedT<label, {\_ -> False}> user m (typ1<selector1 row>, typ2<selector2 row>, typ3<selector3 row>)
@-}
project3
    :: (Monad m, PersistEntity record)
    => ( EntityFieldWrapper user record typ1
       , EntityFieldWrapper user record typ2
       , EntityFieldWrapper user record typ3
       )
    -> Entity record
    -> TaggedT user m (typ1, typ2, typ3)
project3 (field1, field2, field3) record = do
    field1 <- project field1 record
    field2 <- project field2 record
    field3 <- project field3 record
    return (field1, field2, field3)

{-@
projectList2 :: forall < policy1 :: Entity record -> user -> Bool
                       , policy2 :: Entity record -> user -> Bool
                       , selector1 :: Entity record -> typ1 -> Bool
                       , selector2 :: Entity record -> typ2 -> Bool
                       , inverseselector1 :: typ1 -> Entity record -> Bool
                       , inverseselector2 :: typ2 -> Entity record -> Bool
                       , q1 :: typ1 -> Bool
                       , q2 :: typ2 -> Bool
                       , q3 :: typ3 -> Bool
                       , p :: Entity record -> Bool
                       , label :: user -> Bool
                       >.
  { row :: (Entity <p> record) |- {v:(user<label>) | True} <: {v:(user<policy1 row>) | True} }
  { row :: (Entity <p> record) |- typ1<selector1 row> <: typ1<q1> }

  { row :: (Entity <p> record) |- {v:(user<label>) | True} <: {v:(user<policy2 row>) | True} }
  { row :: (Entity <p> record) |- typ2<selector2 row> <: typ2<q2> }

  ( EntityFieldWrapper<policy1, selector1, inverseselector1> user record typ1
  , EntityFieldWrapper<policy2, selector2, inverseselector2> user record typ2
  )
  -> [(Entity <p> record)]
  -> TaggedT<label, {\_ -> False}> user m [(typ1<q1>, typ2<q2>)]
@-}
projectList2
    :: (Monad m, PersistEntity record)
    => (EntityFieldWrapper user record typ1, EntityFieldWrapper user record typ2)
    -> [Entity record]
    -> TaggedT user m [(typ1, typ2)]
projectList2 (field1, field2) records = do
    fields1 <- projectList field1 records
    fields2 <- projectList field2 records
    return $ zip fields1 fields2

{-@
projectList3 :: forall < policy1 :: Entity record -> user -> Bool
                       , policy2 :: Entity record -> user -> Bool
                       , policy3 :: Entity record -> user -> Bool
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
                       , label :: user -> Bool
                       >.
  { row :: (Entity <p> record) |- {v:(user<label>) | True} <: {v:(user<policy1 row>) | True} }
  { row :: (Entity <p> record) |- typ1<selector1 row> <: typ1<q1> }

  { row :: (Entity <p> record) |- {v:(user<label>) | True} <: {v:(user<policy2 row>) | True} }
  { row :: (Entity <p> record) |- typ2<selector2 row> <: typ2<q2> }

  { row :: (Entity <p> record) |- {v:(user<label>) | True} <: {v:(user<policy3 row>) | True} }
  { row :: (Entity <p> record) |- typ3<selector3 row> <: typ3<q3> }

  ( EntityFieldWrapper<policy1, selector1, inverseselector1> user record typ1
  , EntityFieldWrapper<policy2, selector2, inverseselector2> user record typ2
  , EntityFieldWrapper<policy3, selector3, inverseselector3> user record typ3
  )
  -> [(Entity <p> record)]
  -> TaggedT<label, {\_ -> False}> user m [(typ1<q1>, typ2<q2>, typ3<q3>)]
@-}
projectList3
    :: (Monad m, PersistEntity record)
    => ( EntityFieldWrapper user record typ1
       , EntityFieldWrapper user record typ2
       , EntityFieldWrapper user record typ3
       )
    -> [Entity record]
    -> TaggedT user m [(typ1, typ2, typ3)]
projectList3 (field1, field2, field3) records = do
    fields1 <- projectList field1 records
    fields2 <- projectList field2 records
    fields3 <- projectList field3 records
    return $ zip3 fields1 fields2 fields3

{-@
assume selectFirstOr404 :: forall < q  :: Entity record -> user -> Bool
                                  , r1 :: Entity record -> Bool
                                  , r2 :: Entity record -> Bool
                                  , p  :: user -> Bool
                                  >.
  { row :: record
    |- {v:(Entity<r1> record) | entityVal v == row} <: {v:(Entity<r2> record) | True} }

  { row :: (Entity <r2> record)
    |- {v:(user<p>) | True} <: {v:(user<q row>) | True}
  }
  Filter<q, r1> user record -> TaggedT<p, {\v -> v == currentUser 0}> user m (Entity <r2> record)
@-}
selectFirstOr404
    :: ( DB.PersistQueryRead backend
       , DB.PersistRecordBackend record backend
       , MonadReader backend m
       , MonadController w m
       , MonadTIO m
       )
    => Filter user record
    -> TaggedT user m (Entity record)
selectFirstOr404 = selectFirstOr notFound

{-@
assume selectFirstOr :: forall < q  :: Entity record -> user -> Bool
                               , r1 :: Entity record -> Bool
                               , r2 :: Entity record -> Bool
                               , p  :: user -> Bool
                               >.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Response
  -> Filter<q, r1> user record
  -> TaggedT<p, {\v -> v == currentUser 0}> user m (Entity <r2> record)
@-}
selectFirstOr
    :: ( DB.PersistQueryRead backend
       , DB.PersistRecordBackend record backend
       , MonadReader backend m
       , MonadController w m
       , MonadTIO m
       )
    => Response
    -> Filter user record
    -> TaggedT user m (Entity record)
selectFirstOr response filters = do
    maybeRecord <- selectFirst filters
    case maybeRecord of
        Just record -> return record
        Nothing     -> respondTagged response

{-@
insertOrMsg :: forall < p :: Entity record -> Bool
                      , insertpolicy :: Entity record -> user -> Bool
                      , querypolicy  :: Entity record -> user -> Bool
                      , audience :: user -> Bool
                      >.
  { rec :: (Entity<p> record)
      |- {v: user | v == currentUser 0} <: {v: user<insertpolicy rec> | True}
  }

  { rec :: (Entity<p> record)
      |- {v: user<querypolicy p> | True} <: {v: user<audience> | True}
  }
  String
  -> BinahRecord<p, insertpolicy, querypolicy> user record
  -> TaggedT<{\_ -> True}, audience> user m (Maybe (Key record))
@-}
insertOrMsg
  :: ( MonadTIO m
     , DB.PersistStoreWrite backend
     , DB.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => String
  -> BinahRecord user record
  -> TaggedT user m (Maybe (Key record))
insertOrMsg msg row = do
  res <- insertMaybe row
  case res of
    Nothing -> logT Frankie.Log.ERROR msg
    _       -> return ()
  return res