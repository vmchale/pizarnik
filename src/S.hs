module S ( r ) where

import           A
import qualified Data.IntMap as IM
import           Nm

type S = [L]

type F a = IM.IntMap (ASeq a)

r :: F a -> [A a] -> S -> S
r e as = thread (map (ι e) as)
  where thread = foldr (.) id

b :: D b a -> F a -> F a
b (F _ (Nm _ (U i) _) _ as) = IM.insert i as; b TD{} = id

ι :: F a -> A a -> S -> S
ι _ (B _ Dup) (a:as)        = a:a:as
ι _ (B _ Un) (_:as)         = as
ι _ (L _ l) as              = l:as
ι f (V _ (Nm _ (U i) _)) as = r f (aas (f IM.! i)) as
