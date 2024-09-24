{-# LANGUAGE OverloadedStrings #-}

module Pr ( pBound
          , (<#>)
          , (<##>)
          ) where

import qualified Data.IntMap   as IM
import           Prettyprinter (Doc, Pretty (pretty), hardline, vsep, (<+>))

infixr 6 <#>
infixr 6 <##>

(<#>) :: Doc ann -> Doc ann -> Doc ann
x <#> y = x <> hardline <> y

(<##>) :: Doc ann -> Doc ann -> Doc ann
x <##> y = x <> hardline <> hardline <> y

pB :: (Pretty c, Pretty b) => (c, b) -> Doc a
pB (i,j) = pretty i <+> "→" <+> pretty j

pBound :: Pretty b => IM.IntMap b -> Doc a
pBound b = vsep (pB<$>IM.toList b)
