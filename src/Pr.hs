module Pr ( pBound, pB
          , (<#>)
          , (<##>)
          , (<#?>)
          , sq
          ) where

import qualified Data.IntMap   as IM
import           Prettyprinter (Doc, Pretty (pretty), hardline, line, vsep, (<+>))

infixr 6 <#>
infixr 6 <##>
infixr 6 <#?>

(<#>), (<##>), (<#?>) :: Doc ann -> Doc ann -> Doc ann
x <#> y = x <> hardline <> y
x <##> y = x <> hardline <> hardline <> y
x <#?> y = x <> line <> y

pB :: (Pretty c, Pretty b) => (c, b) -> Doc a
pB (i,j) = pretty i <+> "→" <+> pretty j

pBound :: Pretty b => IM.IntMap b -> Doc a
pBound b = vsep (pB<$>IM.toList b)

sq x = "‘" <> x <> "’"
