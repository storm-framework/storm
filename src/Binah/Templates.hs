{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}

module Binah.Templates
  ( TemplateData(..)
  , HasTemplateCache(..)
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

import           Binah.Infrastructure
import           Binah.Filters
import           Binah.Frankie

import           Model

class Mustache.ToMustache d => TemplateData d where
  templateFile :: FilePath

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
    Nothing ->
      liftTIO
        $   TIO
        $   Mustache.compileTemplateWithCache searchDirs oldCache file
        >>= \case
              Right template ->
                let updatedCache = HashMap.insert
                      (Mustache.name template)
                      template
                      (Mustache.partials template)
                in  do
                      modifyMVar_
                        cacheMVar
                        (\currentCache ->
                          evaluate $ currentCache <> updatedCache
                        )
                      pure template
              Left err ->
                error $ "Error parsing template " ++ file ++ ": " ++ show err

{-@ assume renderTemplate :: _ -> TaggedT<{\_ -> True}, {\_ -> False}> _ _ @-}
{-@ ignore renderTemplate @-}
renderTemplate
  :: forall d w m config
   . ( MonadController w m
     , MonadTIO m
     , MonadConfig config m
     , TemplateData d
     , HasTemplateCache config
     )
  => d
  -> TaggedT m Text
renderTemplate templateData = do
  template <- getOrLoadTemplate searchDirs file
  pure $ Mustache.substitute template templateData
 where
  file       = templateFile @d
  searchDirs = ["templates"]
