{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Binah.Templates
  ( HasTemplateCache(..)
  , TemplateData(..)
  , renderTemplate
  )
where

import           Frankie.Config
import qualified Text.Mustache.Types           as Mustache
import qualified Data.HashMap.Strict           as HashMap
import qualified Text.Mustache                 as Mustache
import           Data.Text                      ( Text )
import           Control.Concurrent.MVar        ( MVar
                                                , readMVar
                                                , modifyMVar_
                                                )
import           Control.Exception              ( evaluate )

import qualified Database.Persist              as Persist
import           Database.Persist.Sql           ( fromSqlKey
                                                , SqlBackend
                                                )
import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Frankie

import           Model

class TemplateData d where
  templateFile :: FilePath
  toMustache :: d -> Mustache.Value

class HasTemplateCache config where
  getTemplateCache :: config -> MVar Mustache.TemplateCache

{-@ ignore getOrLoadTemplate @-}
getOrLoadTemplate
  :: (MonadConfig config m, MonadTIO m, HasTemplateCache config)
  => [FilePath]
  -> FilePath
  -> m Mustache.Template
getOrLoadTemplate searchDirs file = do
  cacheMVar <- getTemplateCache <$> getConfig
  oldCache  <- liftTIO $ TIO (readMVar cacheMVar)
  case HashMap.lookup file oldCache of
    Just template -> pure template
    Nothing -> liftTIO $ TIO $ Mustache.compileTemplateWithCache searchDirs oldCache file >>= \case
      Right template -> do
        let updatedCache =
              HashMap.insert (Mustache.name template) template (Mustache.partials template)
        modifyMVar_ cacheMVar (\currentCache -> evaluate $ currentCache <> updatedCache)
        return template
      Left err -> error $ "Error parsing template " ++ file ++ ": " ++ show err

{-@ ignore renderTemplate @-}
{-@ assume renderTemplate :: _ -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
renderTemplate
  :: forall d w m config
   . (MonadTIO m, MonadConfig config m, TemplateData d, HasTemplateCache config)
  => d
  -> TaggedT m Text
renderTemplate templateData = do
  template <- getOrLoadTemplate searchDirs file
  pure $ Mustache.substitute template (toMustache templateData)
 where
  searchDirs = ["templates"]
  file       = templateFile @d


instance Persist.ToBackendKey SqlBackend record => Mustache.ToMustache (Persist.Key record) where
  toMustache id = Mustache.toMustache (show (fromSqlKey id))
