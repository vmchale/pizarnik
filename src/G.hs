module G ( Sn, sn
         , indices
         , setIx
         , gn, gp, gc
         ) where

import qualified Data.Array as A
import           Data.Bits  (Bits (complement, setBit, shiftL, shiftR, testBit, (.&.), (.|.)))
import           Data.List  (foldl')

newtype Sn=Sn Int

sn :: Int -> Sn
sn n = Sn$foldl' (\seed ix -> seed .|. ix `shiftL` (ix*4)) (n `shiftL` 40) [1..n]

indices :: Sn -> [Int]
indices x = [1..gn x]

setIx :: Int -> Int -> Sn -> Sn
setIx ix n (Sn x) = Sn (x .&. complement (0xf `shiftL` (ix*4)) .|. n `shiftL` (ix*4))

gn :: Sn -> Int
gn (Sn n) = n `shiftR` 40

elems :: Sn -> [Int]
elems p = [ p ! i | i <- [1..gn p] ]

(!) :: Sn -> Int -> Int
(Sn x) ! i = (x .&. 0xf `shiftL` (i*4)) `shiftR` (i*4)

gc :: Sn -> [[Int]]
gc p = step 0 1
      where
        n = gn p

        step v j =
            case next j of
                Nothing -> []
                Just j' -> let (v',cyc) = orb v j' in cyc:step v' j'
          where
            next i | i==n = Nothing
                   | testBit v i = next (i+1)
                   | otherwise = Just i

        orb :: Word -> Int -> (Word, [Int])
        orb v j | testBit v j = (v, [])
                | otherwise = let k=p!j; (r, c) = orb (setBit v j) k in (r, j:c)

gp :: Sn -> [a] -> [a]
gp p xs = A.elems (A.array (1, gn p) (zip (elems p) xs))
