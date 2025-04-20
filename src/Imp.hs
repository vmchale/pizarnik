{-# LANGUAGE LambdaCase #-}

module Imp ( resolveI ) where

import           Control.Exception (Exception, throwIO)
import           Control.Monad     (filterM)
import qualified Data.Text         as T
import           Nm
import           Prettyprinter     (Pretty (pretty), (<+>))
import           System.Directory  (doesFileExist)
import           System.FilePath   ((</>))

data IE = IE MN | Amb [FilePath]

instance Pretty IE where pretty (IE mn) = "Module" <+> pretty mn <+> "not found."; pretty (Amb fs) = "Could not disambiguate among candidates " <+> pretty fs

instance Show IE where show=show.pretty
instance Exception IE where

resolveI :: [FilePath] -> MN -> IO FilePath
resolveI is mn = rIIO is mn >>= \case {[] -> throwIO (IE mn); [fp] -> pure fp; fs -> throwIO $ Amb fs}

rIIO :: [FilePath] -> MN -> IO [FilePath]
rIIO incl n = filterM doesFileExist
    . fmap (</> toFileN n) $ incl

toFileN :: MN -> FilePath
toFileN = (<> ".piz") . foldr (</>) mempty . fmap T.unpack . mN
