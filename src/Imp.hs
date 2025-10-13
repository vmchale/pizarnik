{-# LANGUAGE LambdaCase #-}

module Imp ( resolveI ) where

import           Control.Exception  (Exception, throwIO)
import           Control.Monad      (filterM)
import           Data.List          (foldl')
import           Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Text          as T
import           Nm
import           Prettyprinter      (Pretty (pretty), punctuate, (<+>))
import           System.Directory   (doesFileExist)
import           System.Info        (os)

data IE = IE MN | Amb [FilePath]

instance Pretty IE where
    pretty (IE mn)  = "Module" <+> pretty mn <+> "not found."
    pretty (Amb fs) = "Could not disambiguate among candidates: " <+> mconcat (punctuate ", " (pretty<$>fs))

instance Show IE where show=show.pretty
instance Exception IE where

resolveI :: [FilePath] -> MN -> IO FilePath
resolveI is mn = rIIO is mn >>= \case {[] -> throwIO (IE mn); [fp] -> pure fp; fs -> throwIO $ Amb fs}

rIIO :: [FilePath] -> MN -> IO [FilePath]
rIIO incl n = filterM doesFileExist (map (</> toFile n) incl)

toFile :: MN -> FilePath
toFile = (<> ".piz") . (\(x:|xs) -> foldl' (</>) x xs) . fmap T.unpack . mN

(</>) =
  case os of
    "windows" -> \x y -> x ++ "\\" ++ y
    _         -> \x y -> x ++ "/" ++ y
