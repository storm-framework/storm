-- | The various user-accesible primitive operations for interacting with sensitive data.

{-# LANGUAGE GADTs #-}

module Actions where

import Data.Functor.Const (Const(..))
import Control.Monad.Reader (MonadReader(..), runReaderT)
import Database.Persist (PersistQueryRead, PersistRecordBackend, PersistEntity)
import qualified Database.Persist as Persist

import Core
import Model
import Infrastructure
import Filters


{-@ ignore selectList @-}
{-@
assume selectList :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  FilterList<q, r1> record -> TaggedT<p, {\_ -> False}> _ [(Entity <r2> record)]
@-}
selectList :: (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => FilterList record -> TaggedT m [Entity record]
selectList filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectList (toPersistFilters filters) []) backend
  where
    toPersistFilters Empty = []
    toPersistFilters (RefinedFilter f `Cons` filters) = f:(toPersistFilters filters)

{-@ ignore selectFirst @-}
{-@
assume selectFirst :: forall <q :: Entity record -> Entity User -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: Entity User -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <q row> User) | True} }
  FilterList<q, r1> record -> TaggedT<p, {\_ -> False}> _ (Maybe (Entity <r2> record))
@-}
selectFirst :: (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => FilterList record -> TaggedT m (Maybe (Entity record))
selectFirst filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectFirst (toPersistFilters filters) []) backend
  where
    toPersistFilters Empty = []
    toPersistFilters (RefinedFilter f `Cons` filters) = f:(toPersistFilters filters)

{-@ ignore projectList @-}
{-@
assume projectList :: forall <r1 :: Entity record -> Bool, r2 :: typ -> Bool, policy :: Entity record -> Entity User -> Bool, p :: Entity User -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool>.
  { row :: (Entity <r1> record) |- {v:(Entity <p> User) | True} <: {v:(Entity <policy row> User) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  EntityFieldWrapper<policy, selector, inverseselector> record typ ->
  [(Entity <r1> record)] ->
  TaggedT<p, {\_ -> False}> _ [typ<r2>]
@-}
projectList :: (PersistEntity record, Applicative m) => EntityFieldWrapper record typ -> [Entity record] -> TaggedT m [typ]
projectList (EntityFieldWrapper entityField) entities = pure $ map (getConst . Persist.fieldLens entityField Const) entities

{-@
assume printTo :: user:_ -> _ -> TaggedT<{\_ -> True}, {\viewer -> viewer == user}> _ ()
@-}
printTo :: MonadTIO m => Entity User -> String -> TaggedT m ()
printTo user str = liftTIO . TIO . putStrLn . mconcat $
  ["[", userName . entityVal $ user, "] ", str]
