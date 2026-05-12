module Imp ( resolveI ) where

import           Control.Exception  (Exception, throwIO)
import           Control.Monad      (filterM)
import           Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.Text          as T
import           Data.Typeable      (Typeable)
import           Loc
import           Nm
import           Prettyprinter      (Pretty (pretty), punctuate, (<+>))
import           System.Directory   (doesFileExist)
import           System.Info        (os)

data (IE a) = IE (MN a) | Amb [FilePath]

instance Pretty a => Pretty (IE a) where
    pretty (IE mn)  = pretty (ann mn) <> ":" <+> "Module" <+> pretty mn <+> "not found."
    pretty (Amb fs) = "Could not disambiguate among candidates: " <+> mconcat (punctuate ", " (pretty<$>fs))

instance Pretty a => Show (IE a) where show=show.pretty
instance (Pretty a, Typeable a) => Exception (IE a) where

resolveI :: [FilePath] -> MN Loc -> IO FilePath
resolveI is mn = rIIO is mn >>= \case {[] -> throwIO (IE mn); [fp] -> pure fp; fs -> throwIO (Amb fs :: IE Loc)}

rIIO :: [FilePath] -> MN a -> IO [FilePath]
rIIO incl n = filterM doesFileExist (map (</> toFile n) incl)

toFile :: MN a -> FilePath
toFile = (<> ".piz") . (\(x:|xs) -> foldl' (</>) x xs) . fmap T.unpack . mN

(</>) =
  case os of
    "windows" -> \x y -> x ++ "\\" ++ y
    _         -> \x y -> x ++ "/" ++ y
