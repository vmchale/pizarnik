module G ( gp ) where

import qualified Data.Array as A
import qualified Data.Array.Unboxed as UA

gp :: UA.UArray Word Word -> [a] -> [a]
gp p xs = A.elems (A.array (UA.bounds p) (zip (UA.elems p) xs))
