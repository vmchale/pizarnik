module S ( r ) where

import           A
import qualified Data.IntMap as IM
import           Nm

type S = [L]

-- what about atoms in modules
type F a = IM.IntMap (ASeq a)

r :: F (TS a) -> [A (TS a)] -> S -> S
r e as = thread (map (ι e) as)

b :: D b a -> F a -> F a
b (F _ (Nm _ (U i) _) _ as) = IM.insert i as; b TD{} = id

ι :: F (TS a) -> A (TS a) -> S -> S
ι _ (B _ Dup) (a:as)        = a:a:as
ι _ (B _ Un) (_:as)         = as
ι _ (L _ l) as              = l:as
ι f (V _ (Nm _ (U i) _)) as = r f (aas (f IM.! i)) as

thread = foldr (.) id
