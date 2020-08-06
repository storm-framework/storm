{-# LANGUAGE GADTs #-}

{-@ LIQUID "--no-pattern-inline" @-}

module Binah.Updates
  ( assign
  , updateWhere
  , combine
  )
where

import           Control.Monad.Reader
import           Database.Persist               ( PersistRecordBackend
                                                , PersistField
                                                )
import qualified Database.Persist              as Persist

import           Binah.Core
import           Binah.Filters
import           Binah.Infrastructure

{-@
data Update user record < visibility :: Entity record -> user -> Bool
                        , update :: Entity record -> Bool
                        , capabilities :: Entity record -> Bool
                        , policy :: Entity record -> Entity record -> user -> Bool
                        > = Update _ @-}
data Update user record = Update [Persist.Update record]
{-@ data variance Update invariant invariant invariant invariant invariant invariant @-}


-- For some reason the type is not exported if we use `=.`
{-@ ignore assign @-}
{-@
assume assign :: forall < policy :: Entity record -> user -> Bool
                        , selector :: Entity record -> typ -> Bool
                        , flippedselector :: typ -> Entity record -> Bool
                        , r :: typ -> Bool
                        , update :: Entity record -> Bool
                        , fieldref :: typ -> Bool
                        , updatepolicy :: Entity record -> Entity record -> user -> Bool
                        , capability :: Entity record -> Bool
                        >.
  { row :: (Entity record)
  , value :: typ<r>
  , field :: {field:(typ<selector row>) | field == value}
      |- {v:(Entity <flippedselector field> record) | True} <: {v:(Entity <update> record) | True}
  }

  EntityFieldWrapper<policy, selector, flippedselector, capability, updatepolicy> user record typ
  -> typ<r>
  -> Update<policy, update, capability, updatepolicy> user record
@-}
assign :: PersistField typ => EntityFieldWrapper user record typ -> typ -> Update user record
assign (EntityFieldWrapper field) val = Update [field Persist.=. val]


-- TODO: It's probably important to make sure multiple updates to the same field don't happen at once
{-@ ignore combine @-}
{-@
assume combine :: forall < visibility1 :: Entity record -> user -> Bool
                         , visibility2 :: Entity record -> user -> Bool
                         , visibility  :: Entity record -> user -> Bool
                         , update1 :: Entity record -> Bool
                         , update2 :: Entity record -> Bool
                         , update  :: Entity record -> Bool
                         , cap1 :: Entity record -> Bool
                         , cap2 :: Entity record -> Bool
                         , cap  :: Entity record -> Bool
                         , policy1 :: Entity record -> Entity record -> user -> Bool
                         , policy2 :: Entity record -> Entity record -> user -> Bool
                         , policy  :: Entity record -> Entity record -> user -> Bool
                         >.
  { row :: (Entity<update> record)
      |- {v:(user<visibility1 row>) | True} <: {v:(user<visibility row>) | True}
  }
  { row :: (Entity<update> record)
      |- {v:(user<visibility2 row>) | True} <: {v:(user<visibility row>) | True}
  }

  { {v: (Entity<update> record) | True } <: {v: (Entity<update1> record) | True}}
  { {v: (Entity<update> record) | True } <: {v: (Entity<update2> record) | True}}
  { row1 :: (Entity<update1> record)
  , row2 :: (Entity<update2> record)
      |- {v:(Entity record) | v == row1 && v == row2} <: {v:(Entity<update> record) | True}
  }

  { {v: (Entity<cap> record) | True} <: {v: (Entity<cap1> record) | True} }
  { {v: (Entity<cap> record) | True} <: {v: (Entity<cap2> record) | True} }
  { row1 :: (Entity<cap1> record)
  , row2 :: (Entity<cap2> record)
      |- {v:(Entity record) | v == row1 && v == row2} <: {v:(Entity<cap> record) | True}
  }

  { old :: Entity record
  , new :: Entity record
     |- {v: (user<policy old new>) | True } <: {v: (user<policy1 old new>) | True}
  }
  { old :: Entity record , new :: Entity record
     |- {v: (user<policy old new>) | True } <: {v: (user<policy2 old new>) | True}
  }
  { old :: Entity record
  , new :: Entity record
  , user1 :: (user<policy1 old new>)
  , user2 :: (user<policy2 old new>)
      |- {v:(user) | v == user1 && v == user2} <: {v:(user<policy old new>) | True}
  }

  Update<visibility1, update1, cap1, policy1> user record
  -> Update<visibility2, update2, cap2, policy2> user record
  -> Update<visibility,  update,  cap,  policy> user record
@-}
combine :: Update user record -> Update user record -> Update user record
combine (Update us1) (Update us2) = Update (us1 ++ us2)


-- TODO: Figure out what to do with the key
{-@ ignore updateWhere @-}
{-@
assume updateWhere :: forall < visibility :: Entity record -> user -> Bool
                             , update :: Entity record -> Bool
                             , audience :: user -> Bool
                             , capabilities :: Entity record -> Bool
                             , updatepolicy :: Entity record -> Entity record -> user -> Bool
                             , querypolicy :: Entity record -> user -> Bool
                             , filter :: Entity record -> Bool
                             , level :: user -> Bool
                             >.

  { old  :: (Entity<filter> record)
  , new  :: (Entity<update> record)
  , user :: {v: (user<updatepolicy old new>) | v == currentUser 0}
      |- {v:(Entity record) | v == old} <: {v:(Entity<capabilities> record) | True}
  }

  { row :: (Entity<update> record)
      |- {v:(user<visibility row>) | True} <: {v:(user<audience>) | True}
  }

  { row :: (Entity<filter> record)
      |- {v:(user<level>) | True} <: {v:(user<querypolicy row>) | True}
  }

  Filter<querypolicy, filter> user record
  -> Update<visibility, update, capabilities, updatepolicy> user record
  -> TaggedT<level, audience> user m ()
@-}
updateWhere
  :: ( MonadTIO m
     , Persist.PersistQueryWrite backend
     , Persist.PersistRecordBackend record backend
     , MonadReader backend m
     )
  => Filter user record
  -> Update user record
  -> TaggedT user m ()
updateWhere (Filter filters) (Update up) = do
  backend <- ask
  liftTIO (TIO $ runReaderT (Persist.updateWhere filters up) backend)
