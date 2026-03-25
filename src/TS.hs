module TS ( tsort ) where

import qualified Data.Array  as A
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import           Nm

data Tree a = Node a [Tree a]

type N = Int
type Graph = A.Array N [N]

-- children before ancestors
ord :: [Tree a] -> [a]
ord = reverse.ps [] where
    ps es []     = es
    ps es (t:ts) = ps (p es t) ts

    p es (Node x xs) = x:ps es xs

tsr :: Graph -> [N] -> [N]
tsr g = ord.prune.map flower
  where
    flower :: N -> Tree N
    flower x = Node x (map flower (g A.! x))

    prune :: [Tree N] -> [Tree N]
    prune = fst.snip IS.empty where
        snip :: IS.IntSet -> [Tree N] -> ([Tree N], IS.IntSet)
        snip s [] = ([], s)
        snip v (Node x ts:us) | x `IS.member` v = snip v us
                              | otherwise = let (ts',v') = snip (IS.insert x v) ts
                                                (us',v'') = snip v' us
                                            in (Node x ts' : us', v'')

tsort :: [(MN a, [MN a])] -> [U] -> [MN a]
tsort adjL rs = (tbl IM.!) <$> tsr g (unU<$>rs)
    where g = A.array (1,m) (map (\(mn,is) -> (mi mn, map mi is)) adjL)
          (m,tbl) = let al = map ((\mn -> (mi mn,mn)).fst) adjL
                        in (maximum (fst<$>al), IM.fromList al)
          mi=unU.mU
