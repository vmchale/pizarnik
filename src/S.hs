module S ( Ctx, F, S, lm, r, stack ) where

import           A
import           Data.Functor  (($>))
import qualified Data.IntMap   as IM
import           Data.List     (find)
import           Data.Tree     (Tree (Node))
import           F
import           G
import           Nm
import qualified Nm.Map        as Nm
import           Pr
import           Prettyprinter (Doc, pretty)

type S a = [A (TS a)]

type F a = IM.IntMap (ASeq a)
type MC a = Tree (F a, IM.IntMap Int)
type Ctx a = [MC a]

r :: Ctx (TS a) -> [A (TS a)] -> S a -> S a
r e as = thread (map (ι e) (reverse as))

lm :: M b a -> F a
lm (M _ ds) = thread (map b ds) IM.empty

b :: D b a -> F a -> F a
b (F _ (Nm _ (U i) _) _ as) = IM.insert i as; b TD{} = id

i_ c a | [L t (I i)] <- ι c a [] = (i,t)

ta l=let nm=true l;t=TS [] [TT l nm] in C t (nm$>t)
fa l=let nm=false l;t=TS [] [TT l nm] in C t (nm$>t)

i2 c op (a0:a1:as) = let (i0,_)=i_ c a0;(i1,t)=i_ c a1 in L t (I$i1`op`i0):as
ib c rel (a0:a1:as) = let (i0,_)=i_ c a0;(i1,TS _ rs)=i_ c a1 in bt (tL$head rs) (i1`rel`i0):as
    where bt l True= ta l
          bt l False = fa l

(≺) :: T a -> T a -> Bool
(TT _ tt₀) ≺ (TT _ tt₁) | tt₀==tt₁ = True
(TT _ tt) ≺ (Σ _ σ)     | tt `Nm.member` σ = True
_ ≺ _                   = False

-- (precisely why stack-based is interesting, inverse is application...?)

ψ :: Ctx (TS a) -> [ASeq (TS a)] -> S a -> S a
ψ c aa (k:as) | t <- last (trights (aL k)), Just as₀ <- find (h t) (map aas aa) = r c (tail as₀) as -- FIXME: tail assumes one (count types on right)
  where
    h t (a:_) | t' <- last (tlefts (aL a)), t ≺ t' = True
              | otherwise = False

ι :: Ctx (TS a) -> A (TS a) -> S a -> S a
ι _ (B _ Dup) (a:as)       = a:a:as
ι _ (B _ Un) (_:as)        = as
ι c (B _ Plus) as          = i2 c (+) as
ι c (B _ Minus) as         = i2 c (-) as
ι c (B _ Mul) as           = i2 c (*) as
ι c (B _ Div) as           = i2 c quot as
ι c (B _ Rem) as           = i2 c rem as
ι c (B _ Eq) as            = ib c (==) as
ι c (B _ Gt) as            = ib c (>) as
ι c (B _ Lt) as            = ib c (<) as
ι c (B _ Doll) (Q _ a:as)  = r c (aas a) as
ι c (B _ Dip) (Q _ f:a:as) = a:r c (aas f) as
ι _ (L _ (S p)) a          = let n = gn p; (x,a_)=splitAt n a in gp p x++a_
ι _ a@L{} as               = a:as
ι _ a@Q{} as               = a:as
ι _ a@C{} as               = a:as
ι c (Pat _ (SL _ aa)) as   = ψ c aa as -- FIXME: this pinches off stack variables...
ι c (V _ n) as             = let (c',a) = lV c n in r [c'] (aas a) as
ι _ (Inv _ (C _ tt₀)) (C _ tt₁:as) | tt₀==tt₁ = as
ι c a₀@Inv{} (a₁@Inv{}:as) = r c [a₀,a₁] as

lV :: Ctx a -> Nm a -> (MC a, ASeq a)
lV (c:cs) n | Just (c',a) <- lVm c n = (c',a)
            | otherwise = lV cs n
lV [] _ = error"internal error: variable not found."

lVm c@(Node (t,_) s) (Nm _ (U u) _) | Just a <- t IM.!? u = Just (c,a)
                                    | otherwise = tr s
  where
    tr [] = Nothing -- error"internal error: variable not found."
    tr (c'@(Node (m,_) _):cs) | Just a <- m IM.!? u = Just (c',a)
                              | otherwise = tr cs

stack :: S a -> Doc ann
stack = p.reverse where
    p []     = "----"
    p (l:ls) = pretty l <#> p ls
