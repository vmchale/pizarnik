module TS ( tsort ) where

import           Control.Monad.ST (ST, runST)
import qualified Data.Array       as A
import qualified Data.Array.ST    as ST
import qualified Data.IntMap      as IM
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

(!) :: ST.STArray s Int Bool -> Int -> ST s Bool
xs ! n = ST.readArray xs n

tsr :: Graph -> [N] -> [N]
tsr g = ord.prune.map flower
  where
    flower :: N -> Tree N
    flower x = Node x (map flower (g A.! x))

    prune :: [Tree N] -> [Tree N]
    prune f = runST $ do
        seen <- ST.newArray (l,n) False
        let snip [] = pure []
            snip (Node x ts:us) = do
                b <- seen ! x
                if b
                    then snip us
                    else do {ST.writeArray seen x True; ts' <- snip ts; us' <- snip us; pure (Node x ts' : us')}
        snip f

    (l,n) = A.bounds g

tsort :: [(MN a, [MN a])] -> [U] -> [MN a]
tsort adjL rs = (tbl IM.!) <$> tsr g (unU<$>rs)
    where g = A.array (1,m) (map (\(mn,is) -> (mi mn, map mi is)) adjL)
          (m,tbl) = let al = map ((\mn -> (mi mn,mn)).fst) adjL
                        in (maximum (fst<$>al), IM.fromList al)
          mi=unU.mU
