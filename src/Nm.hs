{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}

module Nm ( U (..), Nm (..), MN (..) ) where

import           Data.Foldable      (toList)
import           Data.List          (intersperse)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.Text          as T
import           Prettyprinter      (Doc, Pretty (..))

newtype U = U { unU :: Int } deriving (Eq, Ord)

data MN = MN { mN :: NonEmpty T.Text, mU :: !U }
data Nm a = Nm { text :: T.Text, un :: !U, loc :: a } deriving (Functor, Foldable, Traversable)

intercalate :: Doc a -> [Doc a] -> Doc a
intercalate x = mconcat . intersperse x

instance Eq MN where (==) (MN _ u) (MN _ u') = u == u'
instance Ord MN where compare (MN _ u) (MN _ u') = compare u u'

instance Eq (Nm a) where (==) (Nm _ u _) (Nm _ u' _) = u == u'
instance Ord (Nm a) where compare (Nm _ u _) (Nm _ u' _) = compare u u'

instance Pretty (Nm a) where
    pretty (Nm t _ _) = pretty t
    -- pretty (Nm t (U u) _) = pretty t <> pᵤ u

instance Show (Nm a) where show=show.pretty

instance Pretty MN where
    pretty (MN t _) = intercalate "/" (toList (pretty <$> t))

instance Show MN where show=show.pretty
