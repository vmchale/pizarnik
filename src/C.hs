module C ( pᵤ ) where

import           Data.Function (fix)
import           Data.String   (IsString)

pᵤ :: (Integral a, IsString b, Semigroup b) => a -> b
pᵤ = fix (\r d -> let (q,s) = d `quotRem` 10 in if q==0 then g s else r q<>g s)
  where
    g 0="₀"; g 1="₁"; g 2="₂"; g 3="₃"; g 4="₄";
    g 5="₅"; g 6="₆"; g 7="₇"; g 8="₈"; g 9="₉"
    g _=error "?"
