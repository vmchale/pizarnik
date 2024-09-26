{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}

module Nm ( U (..), Nm (..), MN (..) ) where

import           Data.Foldable      (toList)
import           Data.Function      (fix)
import           Data.List          (intersperse)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.Text          as T
import           Prettyprinter      (Doc, Pretty (..))

newtype U = U { unU :: Int } deriving (Eq, Ord)

data MN = MN { mN :: NonEmpty T.Text, mU :: !U }
data Nm a = Nm { text :: T.Text, un :: !U, loc :: a } deriving (Functor, Foldable, Traversable)

intercalate :: Doc a -> [Doc a] -> Doc a
intercalate x = mconcat . intersperse x

instance Eq MN where
    (==) (MN _ u) (MN _ u') = u == u'

instance Ord MN where
    compare (MN _ u) (MN _ u') = compare u u'

instance Eq (Nm a) where
    (==) (Nm _ u _) (Nm _ u' _) = u == u'

instance Ord (Nm a) where
    compare (Nm _ u _) (Nm _ u' _) = compare u u'

instance Pretty (Nm a) where
    pretty (Nm t _ _) = pretty t
    -- pretty (Nm t (U u) _) = pretty t <> pᵤ u

instance Show (Nm a) where show=show.pretty

instance Pretty MN where
    pretty (MN t _) = intercalate "/" (toList (pretty <$> t))

instance Show MN where show=show.pretty

pᵤ :: Integral a => a -> Doc ann
pᵤ = fix (\r d -> let (q,s) = d `quotRem` 10 in if q==0 then g s else r q<>g s)
  where
    g 0="₀"; g 1="₁"; g 2="₂"; g 3="₃"; g 4="₄";
    g 5="₅"; g 6="₆"; g 7="₇"; g 8="₈"; g 9="₉"
    g _=error "?"
