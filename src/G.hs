module G ( Sn, sn
         , indices
         , setIx
         , gn, gp
         ) where

import qualified Data.Array     as A
import           Data.Bifunctor (second)
import           Data.Bits      (Bits (complement, setBit, shiftL, shiftR, testBit, (.&.), (.|.)))
import           Data.List      (foldl')
import           Prettyprinter  (Pretty (pretty), parens)

newtype Sn=Sn Int

instance Pretty Sn where
    pretty=foldMap (\case [_] -> ""; cyc -> parens (foldMap pretty cyc)).gc
      where
        gc p = step 0 1
              where
                n = gn p

                step v j | j==n = []
                         | testBit v j = step v (j+1)
                         | otherwise = let (v',cyc) = orb v j in cyc:step v' j

                orb :: Word -> Int -> (Word, [Int])
                orb v j | testBit v j = (v, [])
                        | otherwise = let (r, c) = orb (setBit v j) (p!j) in (r, j:c)

sn :: Int -> Sn
sn n = Sn$foldl' (\acc ix -> acc .|. ix `shiftL` (ix*4)) (n `shiftL` 40) [1..n]

indices :: Sn -> [Int]
indices x = [1..gn x]

setIx :: Int -> Int -> Sn -> Sn
setIx ix n (Sn x) = Sn (x .&. complement (0xf `shiftL` (ix*4)) .|. n `shiftL` (ix*4))

gn :: Sn -> Int
gn (Sn n) = n `shiftR` 40

(!) :: Sn -> Int -> Int
(Sn x) ! i = (x .&. 0xf `shiftL` (i*4)) `shiftR` (i*4)

gp :: Sn -> [a] -> [a]
gp p xs = A.elems (A.array (1, gn p) (zip ((p!)<$>[1..]) xs))
