module S ( Ctx, S, lm, r ) where

import           A
import qualified Data.IntMap as IM
import           Data.Tree   (Tree (Node))
import           Nm

type S a = [A (TS a)]

type F a = IM.IntMap (ASeq a)
type Ctx a = Tree (F a)

r :: Ctx (TS a) -> [A (TS a)] -> S a -> S a
r e as = thread (map (ι e) (reverse as))

lm :: M b a -> F a
lm (M _ ds) = thread (map b ds) IM.empty

b :: D b a -> F a -> F a
b (F _ (Nm _ (U i) _) _ as) = IM.insert i as; b TD{} = id

i_ c a | [L t (I i)] <- ι c a [] = (i,t)

i2 c op (a0:a1:as) = let (i0,_)=i_ c a0;(i1,t)=i_ c a1 in L t (I$i1`op`i0):as

ι :: Ctx (TS a) -> A (TS a) -> S a -> S a
ι _ (B _ Swap) (a0:a1:as)  = a1:a0:as
ι _ (B _ Dup) (a:as)       = a:a:as
ι _ (B _ Un) (_:as)        = as
ι c (B _ Plus) as          = i2 c (+) as
ι c (B _ Minus) as         = i2 c (-) as
ι c (B _ Mul) as           = i2 c (*) as
ι c (B _ Div) as           = i2 c quot as
ι c (B _ Doll) (Q _ a:as)  = r c (aas a) as
ι c (B _ Dip) (Q _ f:a:as) = a:r c (aas f) as
ι _ a@L{} as               = a:as
ι _ a@Q{} as               = a:as
ι _ a@C{} as               = a:as
ι c (V _ n) as             = let (c',a) = lV c n in r c' (aas a) as

lV :: Ctx a -> Nm a -> (Ctx a, ASeq a)
lV c@(Node t s) (Nm _ (U u) _) | Just a <- t IM.!? u = (c,a)
                               | otherwise = tr s
  where
    tr [] = error"internal error: variable not found."
    tr (c'@(Node m _):cs) | Just a <- m IM.!? u = (c',a)
                          | otherwise = tr cs

thread = foldr (.) id
