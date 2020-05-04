-- | The various user-accesible primitive operations for interacting with sensitive data.

{-# LANGUAGE GADTs #-}

module Binah.Actions where

import Data.Functor.Const (Const(..))
import Control.Monad.Reader (MonadReader(..), runReaderT)
import Database.Persist (PersistQueryRead, PersistRecordBackend, PersistEntity)
import qualified Database.Persist as Persist
import qualified Data.Text as Text
import Data.Text (Text)

import Binah.Core
import Binah.Infrastructure
import Binah.Filters


{-@ ignore selectList @-}
{-@
assume selectList :: forall <q :: Entity record -> user -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: user -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Filter<q, r1> user record -> TaggedT<p, {\_ -> False}> user _ [(Entity <r2> record)]
@-}
selectList :: (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => Filter user record -> TaggedT user m [Entity record]
selectList filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectList (toPersistFilters filters) []) backend

{-@ ignore selectFirst @-}
{-@
assume selectFirst :: forall <q :: Entity record -> user -> Bool, r1 :: Entity record -> Bool, r2 :: Entity record -> Bool, p :: user -> Bool>.
  { row :: record |- {v:(Entity <r1> record) | entityVal v == row} <: {v:(Entity <r2> record) | True} }
  { row :: (Entity <r2> record) |- {v:(user<p>) | True} <: {v:(user<q row>) | True} }
  Filter<q, r1> user record -> TaggedT<p, {\_ -> False}> user _ (Maybe (Entity <r2> record))
@-}
selectFirst :: (PersistQueryRead backend, PersistRecordBackend record backend, MonadReader backend m, MonadTIO m) => Filter user record -> TaggedT user m (Maybe (Entity record))
selectFirst filters = do
  backend <- ask
  liftTIO . TIO $ runReaderT (Persist.selectFirst (toPersistFilters filters) []) backend

{-@ ignore project @-}
{-@
assume project :: forall <policy :: Entity record -> user -> Bool,
                          selector :: Entity record -> typ -> Bool,
                          flippedselector :: typ -> Entity record -> Bool,
                          r :: Entity record -> Bool,
                          label :: user -> Bool>.
  {row :: (Entity<r> record) |- {v:(user<label>) | True} <: {v:(user<policy row>) | True}}
  {row :: (Entity<r> record) |- {v:(user<policy row>) | True} <: {v:(user<label>) | True}}
  EntityFieldWrapper<policy, selector, flippedselector> user record typ ->
  row:(Entity<r> record) ->
  TaggedT<label, {\_ -> False}> user _ (typ<selector row>)
@-}
project :: (PersistEntity record, Applicative m) => EntityFieldWrapper user record typ -> Entity record -> TaggedT user m typ
project (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectId @-}
{-@
assume projectId :: forall <policy :: Entity record -> user -> Bool, selector :: Entity record -> Key record -> Bool, inverseselector :: Key record -> Entity record -> Bool>.
  EntityFieldWrapper<policy, selector, inverseselector> user record (Key record) -> row:_ -> TaggedT<{\_ -> True}, {\_ -> False}> user _ {v:_ | v == entityKey row}
@-}
projectId :: (PersistEntity record, Applicative m) => EntityFieldWrapper user record (Key record) -> Entity record -> TaggedT user m (Key record)
projectId (EntityFieldWrapper entityField) = pure . getConst . Persist.fieldLens entityField Const

{-@ ignore projectList @-}
{-@
assume projectList :: forall <r1 :: Entity record -> Bool, r2 :: typ -> Bool, policy :: Entity record -> user -> Bool, p :: user -> Bool, selector :: Entity record -> typ -> Bool, inverseselector :: typ -> Entity record -> Bool>.
  { row :: (Entity <r1> record) |- {v:(user<p>) | True} <: {v:(user<policy row>) | True} }
  { row :: (Entity <r1> record) |- typ<selector row> <: typ<r2> }
  EntityFieldWrapper<policy, selector, inverseselector> user record typ ->
  [(Entity <r1> record)] ->
  TaggedT<p, {\_ -> False}> user _ [typ<r2>]
@-}
projectList :: (PersistEntity record, Applicative m) => EntityFieldWrapper user record typ -> [Entity record] -> TaggedT user m [typ]
projectList (EntityFieldWrapper entityField) entities = pure $ map (getConst . Persist.fieldLens entityField Const) entities

{-@
assume printTo :: user:_ -> _ -> TaggedT<{\_ -> True}, {\viewer -> viewer == user}> user _ ()
@-}
printTo :: MonadTIO m => user -> String -> TaggedT user m ()
printTo user = liftTIO . TIO . putStrLn 
  -- TODO: we coul implement this with a typeclass for user
  -- ["[", Text.unpack . userName . Persist.entityVal $ user, "] ", str]
