-- | The various user-accesible primitive operations for interacting with sensitive data.

{-# LANGUAGE GADTs #-}

module Binah.Actions where

import           Data.Functor.Const             ( Const(..) )
import           Control.Monad.Reader           ( MonadReader(..)
                                                , runReaderT
                                                )
import           Database.Persist               ( PersistQueryRead
                                                , PersistRecordBackend
                                                , PersistEntity
                                                )
import qualified Database.Persist              as Persist
import qualified Data.Text                     as Text
import           Data.Text                      ( Text )

import           Binah.Core
import           Binah.Infrastructure
import           Binah.Filters
import           Model


{-@ ignore selectList @-}
{-@
assume selectList :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  Filter<q, r1> record -> TaggedT<p, {\_ -> False}> _ [(Entity <r2> record)]
@-}
selectList
  :: ( PersistQueryRead backend
     , PersistRecordBackend record backend
     , MonadReader backend m
     , MonadTIO m
     )
  => Filter record
  -> TaggedT m [Entity record]
selectList filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectList (toPersistFilters filters) []) backend


{-@ ignore selectFirst @-}
{-@
assume selectFirst :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  Filter<q, r1> record -> TaggedT<p, {\_ -> False}> _ (Maybe (Entity <r2> record))
@-}
selectFirst
  :: ( PersistQueryRead backend
     , PersistRecordBackend record backend
     , MonadReader backend m
     , MonadTIO m
     )
  => Filter record
  -> TaggedT m (Maybe (Entity record))
selectFirst filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectFirst (toPersistFilters filters) []) backend

{-@ ignore project @-}
{-@
assume project :: forall < policy :: Entity record -> Entity User -> Bool
                         , selector :: Entity record -> typ -> Bool
                         , flippedselector :: typ -> Entity record -> Bool
                         , r :: Entity record -> Bool
                         , label :: Entity User -> Bool
                         , capability :: Entity record -> Bool
                         , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                         >.
  {row :: (Entity<r> record) |- {v:(Entity <label> User) | True} <: {v:(Entity<policy row> User) | True}}
  {row :: (Entity<r> record) |- {v:(Entity<policy row> User) | True} <: {v:(Entity <label> User) | True}}
  EntityFieldWrapper<policy, selector, flippedselector, capability, updatepolicy> record typ 
  -> row:(Entity<r> record) 
  -> TaggedT<label, {\_ -> False}> _ (typ<selector row>)
@-}
project
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper record typ
  -> Entity record
  -> TaggedT m typ
project (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectId @-}
{-@
assume projectId :: forall <policy :: Entity record -> Entity User -> Bool, selector :: Entity record -> Key record -> Bool, inverseselector :: Key record -> Entity record -> Bool>.
  EntityFieldWrapper<policy, selector, inverseselector> record (Key record) -> row:_ -> TaggedT<{\_ -> True}, {\_ -> False}> _ {v:_ | v == entityKey row}
@-}
projectId
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper record (Key record)
  -> Entity record
  -> TaggedT m (Key record)
projectId (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectList @-}
{-@
assume projectList :: forall < r1 :: Entity record -> Bool
                             , r2 :: typ -> Bool
                             , policy :: Entity record -> Entity User -> Bool
                             , p :: Entity User -> Bool
                             , selector :: Entity record -> typ -> Bool
                             , inverseselector :: typ -> Entity record -> Bool
                             , capability :: Entity record -> Bool
                             , updatepolicy :: Entity record -> Entity record -> Entity User -> Bool
                             >.
  { row :: (Entity <r1> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <policy row> User) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  EntityFieldWrapper<policy, selector, inverseselector, capability, updatepolicy> record typ 
  -> [(Entity <r1> record)] 
  -> TaggedT<p, {\_ -> False}> _ [typ<r2>]
@-}
projectList
  :: (PersistEntity record, Applicative m)
  => EntityFieldWrapper record typ
  -> [Entity record]
  -> TaggedT m [typ]
projectList (EntityFieldWrapper entityField) entities =
  pure $ map (getConst . Persist.fieldLens entityField Const) entities

{-@
assume printTo :: user:_ -> _ -> TaggedT<{\_ -> True}, {\viewer -> viewer == user}> _ ()
@-}
printTo :: MonadTIO m => Entity User -> String -> TaggedT m ()
printTo user = liftTIO . TIO . putStrLn
    -- . mconcat
    -- $ ["[", Text.unpack . userName . Persist.entityVal $ user, "] ", str]
