{-# LANGUAGE OverloadedStrings #-}

module Imp ( resolveI ) where

import           Control.Exception      (Exception, throwIO)
import           Control.Monad          (filterM)
import           Control.Monad.IO.Class (MonadIO (..))
import           Data.Maybe             (listToMaybe)
import qualified Data.Text              as T
import           Nm
import           Prettyprinter          (Pretty (pretty), (<+>))
import           System.Directory       (doesFileExist)
import           System.FilePath        ((</>))

newtype IE = IE MN

instance Pretty IE where pretty (IE mn) = "Module" <+> pretty mn <+> "not found."

instance Show IE where show=show.pretty
instance Exception IE where

resolveI :: MonadIO m => [FilePath] -> MN -> m FilePath
resolveI is mn = maybe (liftIO . throwIO $ IE mn) pure =<< rIIO is mn

rIIO :: MonadIO m => [FilePath] -> MN -> m (Maybe FilePath)
rIIO incl n = liftIO
    . fmap listToMaybe
    . filterM doesFileExist
    . fmap (</> toFileN n) $ incl

toFileN :: MN -> FilePath
toFileN = (<> ".piz") . foldr (</>) mempty . fmap T.unpack . mN
