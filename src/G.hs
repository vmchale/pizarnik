module G ( Sn, setIx, indices, gn, gp, gc, sn ) where

import qualified Data.Array as A
import           Data.Bits  (Bits (complement, setBit, shiftL, shiftR, testBit, (.&.), (.|.)))

type Sn=Int

-- dbgBits :: Bits a => a -> IO ()
-- dbgBits p = putStrLn $ "0b" ++ map (\case False->'0';True->'1') [ testBit p i | i <- reverse [0..64] ]

sn :: Int -> Sn
sn n = let p = n `shiftL` 40 in thread [ setIx i i | i <- [1..n] ] p
  where
    thread = foldr (.) id

indices :: Sn -> [Int]
indices x = [1..gn x]

setIx :: Int -> Int -> Sn -> Sn
setIx ix n x = (x .&. complement (0xf `shiftL` (ix*4))) .|. (n `shiftL` (ix*4))
-- TODO: set index (allowing previously set values?)

gn :: Sn -> Int
gn n = n `shiftR` 40

elems :: Sn -> [Int]
elems p = [ p ! i | i <- [1..gn p] ]

-- infixl 9
(!) :: Sn -> Int -> Int
x!i = (x .&. (0xf `shiftL` (i*4))) `shiftR` (i*4)

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
