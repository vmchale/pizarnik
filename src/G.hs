module G ( Sn, gp, gc ) where

import qualified Data.Array         as A
import qualified Data.Array.Unboxed as UA
import           Data.Bits          (Bits (shiftL, (.&.), (.|.)))

-- TODO: permutation itself could be a Word (4-bit integers lol)

type Sn=UA.UArray Int Int

gc :: Sn -> [[Int]]
gc p = step 0 1
      where
        (1,n) = UA.bounds p

        step v j =
            case next j of
                Nothing -> []
                Just j' -> let (v',cyc) = orb v j' in cyc:step v' j'
          where
            next i | i==n = Nothing
                   | v .&. (1 `shiftL` i) /= 0 = next (i+1)
                   | otherwise = Just i

        orb :: Word -> Int -> (Word, [Int])
        orb v j | v .&. (1 `shiftL` j) /= 0 = (v, [])
                | otherwise = let k=p UA.! j; (r, c) = orb (v .|. (1 `shiftL` j)) k in (r, j:c)

gp :: Sn -> [a] -> [a]
gp p xs = A.elems (A.array (UA.bounds p) (zip (UA.elems p) xs))
