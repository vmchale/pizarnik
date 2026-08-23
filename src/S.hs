module S ( MC, F, S, lm, r, stack ) where

import           A
import           B
import           Control.Monad ((<=<))
import           D
import           Data.Functor  (($>))
import qualified Data.IntMap   as IM
import           Data.List     (find)
import           F
import           G
import           Nm
import qualified Nm.Map        as Nm
import           Pr
import           Prettyprinter (Doc, pretty)
import           Ty            (UM)

type S a = [A (TS a)]

type F a = IM.IntMap (ASeq a)
type MC a b = (F a, Cs b, Ar)

r :: MC (TS a) a -> [A (TS a)] -> S a -> UM a (S a)
r e as = threadM (map (ι e) (reverse as))

lm :: M b a -> F a
lm (M _ ds) = thread (map b ds) IM.empty

b :: D b a -> F a -> F a
b (F _ (Nm _ (U i) _) _ as) = IM.insert i as; b TD{} = id

i_ c a = (\case [L t (I i)] -> (i,t)) <$> ι c a []; s_ c a = (\case [L t (Str s)] -> (s,t)) <$> ι c a []

ta l=let nm=true l;t=TS [] [TT l nm] in C t (nm$>t)
fa l=let nm=false l;t=TS [] [TT l nm] in C t (nm$>t)

i2 c op (a0:a1:as) = do (i0,_) <- i_ c a0; (i1,t) <- i_ c a1; pure$L t (I$i1`op`i0):as
ib c rel (a0:a1:as) = do (i0,_) <- i_ c a0; (i1,TS _ rs) <- i_ c a1; pure$bt (tL$head rs) (i1`rel`i0):as
    where bt l True= ta l
          bt l False = fa l

ψ :: MC (TS a) a -> [ASeq (TS a)] -> S a -> UM a (S a)
ψ c@(_,cϵ,_) aa (k:as) | t <- last (trights (aL k)), Just as₀ <- find (h t) (map aas aa) = r c as₀ (k:as)
  where
    h t (a:_) | t' <- last (tlefts (aL a)), t ≺ t' = True
              | otherwise = False

    (TT _ tt₀) ≺ (TT _ tt₁) = tt₀==tt₁
    (TT _ tt) ≺ (Σ _ σ)     = tt `Nm.member` σ
    t₀ ≺ t₁ | Just (TC _ n, s) <- tun t₀, Right t₀' <- β cϵ n s = t₀' ≺ t₁
    t₀ ≺ t₁ | Just (TC _ n, s) <- tun t₁, Right t₁' <- β cϵ n s = t₀ ≺ t₁'
    _ ≺ _                   = False

ι :: MC (TS a) a -> A (TS a) -> S a -> UM a (S a)
ι _ (B _ Dup) (a:as)       = pure (a:a:as)
ι _ (B _ Un) (_:as)        = pure as
ι c (B _ Plus) as          = i2 c (+) as
ι c (B _ Minus) as         = i2 c (-) as
ι c (B _ Mul) as           = i2 c (*) as
ι c (B _ Div) as           = i2 c quot as
ι c (B _ Rem) as           = i2 c rem as
ι c (B _ Eq) as            = ib c (==) as
ι c (B _ Gt) as            = ib c (>) as
ι c (B _ Lt) as            = ib c (<) as
ι c (B _ Cat) (a0:a1:as)   = do (s0,_) <- s_ c a0; (s1,t) <- s_ c a1; pure$L t (Str$s1<>s0):as
ι c (B _ Ap) (Q _ a:as)    = r c (aas a) as
ι c (B _ Dip) (Q _ f:a:as) = (a:) <$> r c (aas f) as -- FIXME: e.g. 15 5 nip leaves 5 on stack but with type 'A Int -- 'A Int Int...
ι _ (L _ (S p)) a          = let n = gn p; (x,a_)=splitAt n a in pure (gp p x++a_)
ι _ a@L{} as               = pure (a:as)
ι _ a@Q{} as               = pure (a:as)
-- FIXME: type catenation? FIXME don't pinch off if there aren't enough...
ι c a@(C (TS _ tr) tt) as  =
    let n=lA c tt; (x,a_)=splitAt n as
        (ᴀ:_)=tr
    in pure (if n==0 then a:as else Ca (TS [ᴀ] tr) (a:x):a_)
ι c (Pat _ (SL _ aa)) as   = ψ c aa as -- FIXME: this pinches off stack variables...?
ι c (V _ n) as             = let a = lV c n in r c (aas a) as
ι _ (Inv _ (C _ tt₀)) (Ca _ (C _ tt₁:cs):as) | tt₀==tt₁ = pure (cs++as)
ι _ (Inv _ (C _ tt₀)) (C _ tt₁:as) | tt₀==tt₁ = pure as
ι c a₀@Inv{} (a₁@Inv{}:as) = r c [a₀,a₁] as
ι _ a₀ aa = error (show (a₀,aa))

lA :: MC a b -> Nm a -> Int
lA (_,_,a) (Nm _ (U u) _) | Just ar <- a IM.!? u = ar
                          | otherwise = ie"arity not found"

lV :: MC a b -> Nm a -> ASeq a
lV (c,_,_) n@(Nm _ (U u) _) | Just a <- c IM.!? u = a
                            | otherwise = ie("variable " ++ show n ++ " not found.")

stack :: S a -> Doc ann
stack = p.reverse where
    p []     = "----"
    p (l:ls) = pretty l <#> p ls

ie s=error("internal error: "++s)

threadM :: Monad m => [a -> m a] -> a -> m a
threadM = foldr (<=<) pure
