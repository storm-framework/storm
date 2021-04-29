{-# LANGUAGE FlexibleContexts #-}
-- | The various user-accesible primitive operations for interacting with sensitive data.

{-# LANGUAGE GADTs #-}

module Storm.Actions where

import           Data.Functor.Const             ( Const(..) )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , runReaderT
                                                )
import           Database.Persist               ( PersistQueryRead
                                                , PersistRecordBackend
                                                , PersistEntity
                                                )
import qualified Database.Persist              as Persist
-- import qualified Database.Persist.Query        as PQ
import qualified Database.Esqueleto            as E
-- import qualified Data.Text                     as Text
-- import           Data.Text                      ( Text )

import           Storm.Core
import           Storm.Infrastructure
import           Storm.Filters


{-@ ignore selectList @-}
{-@
assume selectList :: forall < q  :: Entity record -> user -> Bool
                            , r1 :: Entity record -> Bool
                            , r2 :: Entity record -> Bool
                            , p  :: user -> Bool
                            >.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Filter<q, r1> user record -> TaggedT<p, {\_ -> False}> user _ [(Entity <r2> record)]
@-}
selectList
  :: ( PersistQueryRead backend
     , PersistRecordBackend record backend
     , MonadReader backend m
     , MonadTIO m
     )
  => Filter user record
  -> TaggedT user m [Entity record]
selectList filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectList (toPersistFilters filters) []) backend


{-@ ignore selectFirst @-}
{-@
assume selectFirst :: forall < q  :: Entity record -> user -> Bool
                             , r1 :: Entity record -> Bool
                             , r2 :: Entity record -> Bool
                             , p  :: user -> Bool
                             >.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Filter<q, r1> user record -> TaggedT<p, {\_ -> False}> user _ (Maybe (Entity <r2> record))
@-}
selectFirst
  :: ( PersistQueryRead backend
     , PersistRecordBackend record backend
     , MonadReader backend m
     , MonadTIO m
     )
  => Filter user record
  -> TaggedT user m (Maybe (Entity record))
selectFirst filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectFirst (toPersistFilters filters) []) backend

{-@ ignore count @-}
{-@
assume count :: forall < q :: Entity record -> user -> Bool
                       , r :: Entity record -> Bool
                       , p :: user -> Bool
                       >.
  { row :: (Entity <r> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Filter<q, r> user record -> TaggedT<p, {\_ -> False}> user _ Int
@-}
count
  :: ( PersistQueryRead backend
     , PersistRecordBackend record backend
     , MonadReader backend m
     , MonadTIO m
     )
  => Filter user record
  -> TaggedT user m Int
count filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.count (toPersistFilters filters)) backend

{-@ ignore project @-}
{-@
assume project :: forall < policy :: Entity record -> user -> Bool
                         , selector :: Entity record -> typ -> Bool
                         , flippedselector :: typ -> Entity record -> Bool
                         , r :: Entity record -> Bool
                         , label :: user -> Bool
                         , capability :: Entity record -> Bool
                         , updatepolicy :: Entity record -> Entity record -> user -> Bool
                         >.
  {row :: (Entity<r> record) |- {v:(user<label>) | True} <: {v:(user<policy row>) | True}}
  {row :: (Entity<r> record) |- {v:(user<policy row>) | True} <: {v:(user<label>) | True}}
  EntityFieldWrapper<policy, selector, flippedselector, capability, updatepolicy> user record typ
  -> row:(Entity<r> record)
  -> TaggedT<label, {\_ -> False}> user _ (typ<selector row>)
@-}
project
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper user record typ
  -> Entity record
  -> TaggedT user m typ
project (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectId @-}
{-@
assume projectId :: forall <policy :: Entity record -> user -> Bool, selector :: Entity record -> Key record -> Bool, inverseselector :: Key record -> Entity record -> Bool>.
  EntityFieldWrapper<policy, selector, inverseselector> user record (Key record)
  -> row: Entity record
  -> TaggedT<{\_ -> True}, {\_ -> False}> user _ {v:_ | v == entityKey row}
@-}
projectId
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper user record (Key record)
  -> Entity record
  -> TaggedT user m (Key record)
projectId (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectList @-}
{-@
assume projectList :: forall < r1 :: Entity record -> Bool
                             , r2 :: typ -> Bool
                             , policy :: Entity record -> user -> Bool
                             , p :: user -> Bool
                             , selector :: Entity record -> typ -> Bool
                             , inverseselector :: typ -> Entity record -> Bool
                             , capability :: Entity record -> Bool
                             , updatepolicy :: Entity record -> Entity record -> user -> Bool
                             >.
  { row :: (Entity <r1> record) |- {v:(user<p>) | True} <: {v:(user<policy row>) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  EntityFieldWrapper<policy, selector, inverseselector, capability, updatepolicy> user record typ
  -> [(Entity <r1> record)]
  -> TaggedT<p, {\_ -> False}> user _ [typ<r2>]
@-}
projectList
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper user record typ
  -> [Entity record]
  -> TaggedT user m [typ]
projectList (EntityFieldWrapper entityField) entities =
  pure $ map (getConst . Persist.fieldLens entityField Const) entities

----------------------------------------------------------------------------- 
-- Experimenting with JOIN
----------------------------------------------------------------------------- 
joinWhere
  :: ( PersistQueryRead backend
     , PersistRecordBackend row1 backend
     , PersistRecordBackend row2 backend
     , MonadReader backend m
     , MonadTIO m
     , E.PersistUniqueRead backend
     , E.PersistField ty
     , E.BackendCompatible E.SqlBackend backend
     , E.BackendCompatible E.SqlBackend (E.BaseBackend backend)
     )
  => EntityFieldWrapper user row1 ty 
  -> EntityFieldWrapper user row2 ty
  -> Filter user row1
  -> TaggedT user m [(Entity row1, Entity row2)]
joinWhere (EntityFieldWrapper f1) (EntityFieldWrapper f2) q1 = do
  backend <- ask
  liftTIO . TIO $ runReaderT act backend
  where
    act = E.select $ E.from $ \(r1 `E.InnerJoin` r2) -> do
            E.on $ r1 E.^. f1 E.==. r2 E.^. f2
            E.where_ (filterToSqlExpr q1 r1)
            return (r1, r2)

joinWhereEq 
  :: ( PersistQueryRead backend
     , PersistRecordBackend row1 backend
     , PersistRecordBackend row2 backend
     , MonadReader backend m
     , MonadTIO m
     , E.PersistUniqueRead backend
     , E.PersistField ty
     , E.BackendCompatible E.SqlBackend backend
     , E.BackendCompatible E.SqlBackend (E.BaseBackend backend)
     )
  => EntityFieldWrapper user row1 ty 
  -> EntityFieldWrapper user row2 ty
  -> EntityFieldWrapper user row1 ty 
  -> ty
  -> TaggedT user m [(Entity row1, Entity row2)]
joinWhereEq (EntityFieldWrapper f1) (EntityFieldWrapper f2) (EntityFieldWrapper f1') v1' = do
  backend <- ask
  liftTIO . TIO $ runReaderT act backend
  where
    act = E.select $ E.from $ \(r1 `E.InnerJoin` r2) -> do
            E.on $ r1 E.^. f1 E.==. r2 E.^. f2
            -- IDEALLY, take a `Filter` q1 and E.where_ (_fixme (toPersistFilters q1))
            -- https://github.com/bitemyapp/esqueleto/issues/247
            E.where_ (r1 E.^. f1' E.==. E.val v1') 
            return (r1, r2)

filterToSqlExpr 
  :: (PersistEntity row)
  => Filter user row -> E.SqlExpr (E.Entity row) -> E.SqlExpr (E.Value Bool)
filterToSqlExpr (Filter fs) row = go (Persist.FilterAnd fs) 
  where
    -- go :: Persist.Filter row -> E.SqlExpr (E.Value Bool)
    go (Persist.FilterAnd fs) = foldr (E.&&.) (E.val True)  (go <$> fs)
    go (Persist.FilterOr fs)  = foldr (E.||.) (E.val False) (go <$> fs) 
    go (Persist.Filter fld (Persist.FilterValue val) o) = op o (row E.^.fld) (E.val val)
    op Persist.Eq = (E.==.)
    op Persist.Ne = (E.!=.)
    op Persist.Lt = (E.<.)
    op Persist.Le = (E.<=.)
    op Persist.Gt = (E.>.)
    op Persist.Ge = (E.>=.)
    
    -- go (Persist.Filter fld (Persist.FilterValue val) Persist.Eq) = row E.^.fld E.==. E.val val
    -- go 
-- From: https://www.yesodweb.com/book/sql-joins
