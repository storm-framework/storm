{-# LANGUAGE GADTs #-}

module Binah.Updates where

import Control.Monad.Reader
import Database.Persist (PersistRecordBackend, PersistField)
import qualified Database.Persist as Persist

import Binah.Core
import Binah.Infrastructure
import Model

{-@ newtype Update record <visibility :: record -> Entity User -> Bool, update :: Entity record -> Bool> = Update _ @-}
newtype Update record = Update [Persist.Update record]
{-@ data variance Update invariant covariant invariant @-}

-- TODO: This isn't working and i blame the update part.
{-@ ignore (=.) @-}
{-@
assume (=.) :: forall <policy :: Entity record -> Entity User -> Bool,
                       selector :: Entity record -> typ -> Bool,
                       flippedselector :: typ -> Entity record -> Bool,
                       r :: typ -> Bool,
                       update :: Entity record -> Bool,
                       fieldref :: typ -> Bool>.
  { row :: (Entity record), value :: typ<r> |- {field:(typ<selector row>) | field == value} <: typ<fieldref> }
  { field :: typ<fieldref> |- {v:(Entity <flippedselector field> record) | True} <: {v:(Entity <update> record) | True} }
  EntityFieldWrapper<policy, selector, flippedselector> record typ -> typ<r> -> Update<policy, update> record
@-}
(=.) :: PersistField typ => EntityFieldWrapper record typ -> typ -> Update record
(EntityFieldWrapper field) =. val = Update [field Persist.=. val]

-- TODO: It's probably important to make sure multiple updates to the same field don't happen at once
{-@
instance Semigroup (Update record) where
  assume (<>) :: forall <visibility1 :: Entity record -> Entity User -> Bool,
                         visibility2 :: Entity record -> Entity User -> Bool,
                         visibility :: Entity record -> Entity User -> Bool,
                         update1 :: Entity record -> Bool,
                         update2 :: Entity record -> Bool,
                         update :: Entity record -> Bool>.
    { row :: (Entity <update> record) |- {v:(Entity <visibility1 row> User) | True} <: {v:(Entity <visibility row>) | True} }
    { row :: (Entity <update> record) |- {v:(Entity <visibility2 row> User) | True} <: {v:(Entity <visibility row>) | True} }
    { row1 :: (Entity <update1> record), row2 :: (Entity <update2> record) |- {v:(Entity record) | v == row1 && v == row2} <: {v:(Entity <update> record) | True} }
    { row1 :: (Entity <update1> record), row2 :: (Entity <update2> record) |- {v:(Entity <update> record) | True} <: {v:(Entity record) | v == row1 && v == row2} }
    Update<visibility1, update1> -> Update<visibility2, update2> -> Update<visibility, update>
@-}
instance Semigroup (Update record) where
  (<>) = combineUpdates

-- TODO: Why does this make liquid crash w/out ignore
{-@ ignore combineUpdates @-}
combineUpdates :: Update record -> Update record -> Update record
combineUpdates (Update us1) (Update us2) = Update (us1 ++ us2)


-- TODO: Figure out what to do with the key
{-@
assume update :: forall <visibility :: Entity record -> Entity User -> Bool,
                         update :: Entity record -> Bool,
                         audience :: Entity User -> Bool>.
  { row :: (Entity <update> record) |- {v:(Entity <visibility row> User) | True} <: {v:(Entity <audience> User) | True} }
  key:(Key record) -> Update<visibility, update> record -> TaggedT<{\_ -> True}, audience> m ()
@-}
update :: (MonadTIO m, PersistRecordBackend record backend, MonadReader backend m) =>
          Key record -> Update record -> TaggedT m ()
update = undefined
