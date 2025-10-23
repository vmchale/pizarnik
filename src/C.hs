module C ( pᵤ ) where

import           Data.Function (fix)
import qualified Data.Text     as T

pᵤ :: Int -> T.Text
pᵤ i = if i<0 then "₋" <> p (-i) else p i
  where
    p = fix (\r d -> let (q,s) = d `quotRem` 10 in if q==0 then g s else r q<>g s)
      where
        g c = T.singleton (toEnum (c+8320))
