{-# LANGUAGE OverloadedStrings #-}

module Ty ( TE, Ext (..), tM ) where

import           A
import           B
import           Control.Monad              (unless)
import           Control.Monad.Except       (liftEither, throwError)
import           Control.Monad.State.Strict (StateT, gets, modify, runStateT, state)
import           Data.Bifunctor             (first, second)
import           Data.Foldable              (traverse_)
import           Data.Functor               (($>))
import qualified Data.IntMap                as IM
import qualified Data.Set                   as S
import qualified Data.Text                  as T
import           Nm
import           Pr
import           Prettyprinter              (Doc, Pretty (pretty), hardline, hsep, indent, squotes, (<+>))
import           Ty.Clone

infixr 6 @>
infixl 6 @@
infixr 6 @*

data Ext a = Ext { fns :: IM.IntMap (TS S.Set a), tds :: Cs a }

instance Semigroup (Ext a) where (<>) (Ext f0 td0) (Ext f1 td1) = Ext (f0<>f1) (td0<>td1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty

data TE a = UF (T S.Set a) (T S.Set a) F | MF (T S.Set a) (T S.Set a) F
          | USF (TSeq S.Set a) (TSeq S.Set a) F | MSF (TSeq S.Set a) (TSeq S.Set a) F | BE (BE a)

tLs :: TSeq f a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty (UF t0 t1 f)    = tc t0 f $ "Failed to unify" <+> squotes (pretty t0) <+> "with" <+> squotes (pretty t1)
    pretty (USF ts0 ts1 f) = tsc ts0 f $ "Failed to unify" <+> squotes (pSeq ts0) <+> "with" <+> squotes (pSeq ts1)
    pretty (MF t0 t1 f)    = tc t0 f $ "Failed to match" <+> squotes (pretty t0) <+> "against" <+> squotes (pretty t1)
    pretty (MSF ts0 ts1 f) = tsc ts0 f $ "Failed to match" <+> squotes (pSeq ts0) <+> "against" <+> squotes (pSeq ts1)
    pretty (BE e)          = pretty e

tc t f p = pretty (tL t) <> ":" <+> pretty f <+> p
tsc t f p = pretty (tLs t) <> ":" <+> pretty f <+> p

instance Pretty a => Show (TE a) where show=show.pretty

data F = LF | RF

instance Pretty F where pretty LF="⦠"; pretty RF="∢"

instance Show F where show=show.pretty

data TSt a = TSt { maxT :: !Int, lo :: !(Ext a) }

type TM x = StateT (TSt x) (Either (TE x))

runTM :: Int -> TM a b -> Either (TE a) (b, Ext a, Int)
runTM u = fmap (\(x, TSt m st) -> (x, st, m)).flip runStateT (TSt u (Ext IM.empty IM.empty))

type Bt a = IM.IntMap (T S.Set a)
data Subst a = Subst { tvs :: Bt a, svs :: IM.IntMap (TSeq S.Set a) }

instance Pretty (Subst a) where pretty (Subst t s) = "tv" <#> pBound t <##> "sv" <#> pBound s

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst tv sv) = Subst (f tv) sv; mapSV f (Subst tv sv) = Subst tv (f sv)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
ising n t = Subst IM.empty (IM.singleton (unU$un n) t)

tCtx :: Cs a -> T S.Set a -> Either (BE a) (T S.Set a)
tCtx c t@TC{} = uncurry (β c) (tun t)
tCtx c t@TA{} = uncurry (β c) (tun t)
tCtx _ t      = Right t

tun :: T f a -> (Nm a, [T f a])
tun (TC _ n)     = (n, [])
tun (TA _ t0 t1) = second (++[t1]) (tun t0)

lΒ :: Cs a -> T S.Set a -> TM a (T S.Set a)
lΒ c = liftEither . first BE . tCtx c

iFn :: Nm a -> TS S.Set b -> TM b ()
iFn (Nm _ (U i) _) ts = modify (\(TSt m (Ext f c)) -> TSt m (Ext (IM.insert i ts f) c))

iTD :: Nm a -> [Nm b] -> T S.Set b -> TM b ()
iTD (Nm _ (U i) _) vs t = modify (\(TSt m (Ext f c)) -> TSt m (Ext f (IM.insert i (vs,t) c)))

(@*) :: Subst a -> TS S.Set a -> TM a (TS S.Set a)
s @* (TS l r) = TS <$> s@@l <*> s@@r

{-# SCC (@@) #-}
(@@) :: Subst a -> TSeq S.Set a -> TM a (TSeq S.Set a)
(@@) _ []          = pure []
(@@) s (SV _ n:ts) = do {v <- s@~>n; (v++)<$>s@@ts}
(@@) s (t:ts)      = do {t' <- s@> t; (t':)<$>s@@ts}

(@~>) :: Subst a -> Nm a -> TM a (TSeq S.Set a)
(@~>) s v@(Nm _ (U i) x) =
    case IM.lookup i (svs s) of
        Just ts -> mapSV (IM.delete i) s @@ ts
        Nothing -> pure [SV x v]

{-# SCC (@>) #-}
(@>) :: Subst a -> T S.Set a -> TM a (T S.Set a)
(@>) _ t@TP{}          = pure t
(@>) _ t@TT{}          = pure t
(@>) s t@(TA _ TC{} _) = do
    cs <- gets (tds.lo)
    (s@>) =<< lΒ cs t
(@>) s t@TC{} = do
    cs <- gets (tds.lo)
    (s@>) =<< lΒ cs t
(@>) s (TA x t0 t1)    = TA x <$> s@>t0 <*> s@>t1
(@>) s (QT x sig)      = QT x<$>s@*sig
(@>) s (TI x t)        = TI x <$> s@>t
(@>) s t@(TV _ n)      =
    let u=unU (un n) in
    case IM.lookup u (tvs s) of
        Nothing -> pure t
        Just t' -> mapTV (IM.delete u) s@>t'
(@>) s (Σ x ts) = Σ x <$> tset (s@@) ts
(@>) _ SV{} = error "Internal error: (@>) applied to stack variable "

tset f = fmap S.fromList . traverse f . S.toList

{-# SCC usc #-}
usc :: F -> Subst a -> TSeq S.Set a -> TSeq S.Set a -> TM a (TSeq S.Set a, Subst a)
usc f s = uas f s `onM` (s@@)

{-# SCC uas #-}
uas :: F -> Subst a -> TSeq S.Set a -> TSeq S.Set a -> TM a (TSeq S.Set a, Subst a)
uas _ s [] [] = pure ([], s)
uas f s t0@((SV _ sn0):t0d) t1@((SV _ sn1):t1d) =
    let n0=length t0d; n1=length t1d in
    case compare n0 n1 of
        GT -> let (uws, res) = splitFromLeft n1 t0
              in first (uws++) <$> usc f (iSV sn1 uws s) t1d res
        _ -> let (uws, res) = splitFromLeft n0 t1
             in first (uws++) <$> usc f (iSV sn0 uws s) t0d res
uas f s t0@((SV _ sn0):t0d) t1 =
    let n0=length t0d; n1=length t1 in
    case compare n0 n1 of
        GT -> throwError $ USF t0 t1 f
        _ -> let (uws, res) = splitFromLeft n0 t1
             in first (uws++) <$> usc f (iSV sn0 uws s) t0d res
uas f s t0 t1@((SV _ sn1):t1d) =
    let n0=length t0; n1=length t1d in
    case compare n0 n1 of
        LT -> throwError $ USF t0 t1 f
        _ -> let (uws, res) = splitFromLeft n1 t0
             in first (uws++) <$> usc f (iSV sn1 uws s) t1d res
uas RF s t0 t1 | length t0 > length t1 = pure ([Σ (tLs t0) (S.fromList [t0,t1])], s) -- FIXME don't include prefix-up-to-unfication in arms
               | length t1 > length t0 = pure ([Σ (tLs t1) (S.fromList [t0,t1])], s)
uas f s (t0:ts0) (t1:ts1) = do
    (tϵ, s') <- ua f s t0 t1
    first (tϵ:) <$> usc f s' ts0 ts1
uas f _ t0 [] = throwError $ USF t0 [] f
uas f _ [] t1 = throwError $ USF t1 [] f

{-# SCC uac #-}
uac :: F -> Subst a -> T S.Set a -> T S.Set a -> TM a (T S.Set a, Subst a)
uac f s = ua f s `onM` (s@>)

{-# SCC ua #-}
ua :: F -> Subst a -> T S.Set a -> T S.Set a -> TM a (T S.Set a, Subst a)
ua _ s t@(TP _ p0) (TP _ p1) | p0==p1 = pure (t, s)
ua LF _ t0@TP{} t1@TP{} = throwError $ UF t0 t1 LF
ua _ s t@(TV _ n0) (TV _ n1) | n0 == n1 = pure (t, s)
ua _ s t0 (TV _ n) = pure (t0, iTV n t0 s)
ua _ s (TV _ n) t1 = pure (t1, iTV n t1 s)
ua f s (TA x t0 t1) (TA _ t0' t1') = do
    (t0ϵ, s0) <- ua f s t0 t0'
    (t1ϵ, s1) <- uac f s0 t1 t1'
    pure (TA x t0ϵ t1ϵ, s1)
ua _ s (QT x t0) (QT _ t1) = first (QT x) <$> us s t0 t1
ua _ s t0@(TT _ tt0) (TT _ tt1) | tt0 == tt1 = pure (t0, s)
ua RF s t0@(TT x _) t1@(TT _ _) = pure (Σ x (S.fromList [[t0],[t1]]), s) -- TODO: order... tseq... unifies different length sequences as well (on the right)
ua LF _ t0@TT{} t1@TT{} = throwError $ UF t0 t1 LF
ua RF s (Σ _ ts) t1@(TT x _) = pure (Σ x (S.insert [t1] ts), s)
ua RF s t1@(TT x _) (Σ _ ts) = pure (Σ x (S.insert [t1] ts), s)
ua _ _ t0 t1 = error (show (t0,t1))

mSig :: TS S.Set a -> TS S.Set a -> TM a (Subst a)
mSig (TS l0 r0) (TS l1 r1) = do {s <- ms LF l0 l1; msc RF s r0 r1} -- TODO: msc for constructor application?

msc :: F -> Subst a -> TSeq S.Set a -> TSeq S.Set a -> TM a (Subst a)
msc f s = ms f `onM` (s@@)

ms :: F -> TSeq S.Set a -> TSeq S.Set a -> TM a (Subst a)
ms f t0e@(SV{}:t0) t1e@((SV _ sn1):t1) =
    let n0=length t0; n1=length t1 in
    if n0>n1
        then throwError $ MSF t0e t1e f
        else let (uws, res) = splitFromLeft n0 t1
             in msc f (ising sn1 uws) t0 res
ms f t0e@(SV _ v0:t0) t1 = do
    cs <- gets (tds.lo)
    t1ϵ <- traverse (lΒ cs) t1
    let n0=length t0; n1=length t1ϵ
    if n0>n1
        then throwError $ MSF t0e t1ϵ f
        else let (uws, res) = splitFromLeft n0 t1ϵ
             in msc f (ising v0 uws) t0 res
ms f (t0:ts0) (t1:ts1) = do {s' <- ma f t0 t1; msc f s' ts0 ts1}
-- stitch starting at the right
-- {a `r ⊕ a `g} is a {`r ⊕ `g}
ms _ [] [] = pure mempty
ms f ts0 [] = throwError$ MSF ts0 [] f
ms f [] ts1 = throwError$ MSF ts1 [] f

{-# SCC ma #-}
ma :: F -> T S.Set a -> T S.Set a -> TM a (Subst a)
ma _ (TP _ p0) (TP _ p1) | p0==p1 = pure mempty
ma _ (TT _ n0) (TT _ n1) | n0==n1 = pure mempty
ma _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
ma _ (TV _ n0) t = pure (Subst (IM.singleton (unU$un n0) t) IM.empty)
ma f t0 t1@TV{} = throwError $ MF t0 t1 f
ma _ (QT _ ts0) (QT _ ts1) = mSig ts0 ts1
ma f t0@QT{} t1 = throwError $ MF t0 t1 f
-- on the left: intersection (type annotation must be narrower than what it accepts)
-- on the right: type annotation can be more general (superset)
ma LF t0@(Σ _ σ0) t1@(Σ _ σ1) = unless (σ1 `S.isSubsetOf` σ0) (throwError $ MF t0 t1 LF) $> mempty
ma RF t0@(Σ _ σ0) t1@(Σ _ σ1) = unless (σ0 `S.isSubsetOf` σ1) (throwError $ MF t0 t1 RF) $> mempty
ma LF t0@TT{} t1@Σ{} = throwError $ MF t0 t1 LF
ma _ (TC _ n0) (TC _ n1) | n0==n1 = pure mempty
ma f t0 t1@TC{} = do
    cs <- gets (tds.lo)
    t1' <- lΒ cs t1
    ma f t0 t1'
ma f t0 (TA _ TC{} _) = do
    cs <- gets (tds.lo)
    t1' <- lΒ cs t0
    ma f t0 t1'

mtsc :: Subst a -> TS S.Set a -> TS S.Set a -> TM a (Subst a)
mtsc s asig tsig = do {asig' <- s@*asig; mSig asig' tsig}

us :: Subst a -> TS S.Set a -> TS S.Set a -> TM a (TS S.Set a, Subst a)
us s (TS l0 r0) (TS l1 r1) = do {(l,s') <- usc LF s l0 l1; (r,s'') <- usc RF s' r0 r1; pure (TS l r, s'')}

liftClone :: TS S.Set a -> TM a (TS S.Set a)
liftClone ts = do {u <- gets maxT; let (w, ts') = cloneSig u ts in modify (\s -> s {maxT = w}) $> ts'}

lA :: IM.IntMap (TS S.Set a) -> Nm a -> TM a (TS S.Set a)
lA es (Nm _ (U i) _) = do
    b <- gets (fns.lo)
    case IM.lookup i b of
        Just ts -> liftClone ts
        Nothing -> case IM.lookup i es of
            Just ts -> liftClone ts
            Nothing -> pure $ IM.findWithDefault (error "Internal error. Name lookup failed during type resolution.") i es

tM :: Int -> Ext a -> M [] a a -> Either (TE a) (M S.Set a (TS S.Set a), Ext a, Int)
tM i ex = runTM i.tMM ex

tMM :: Ext a -> M [] a a -> TM a (M S.Set a (TS S.Set a))
tMM b (M is ds) = M is <$> tD b ds

tD :: Ext a -> [D [] a a] -> TM a [D S.Set a (TS S.Set a)]
tD b ds = traverse_ tD0 ds *> traverse (tD1 b) ds

tD0 :: D [] a a -> TM a ()
tD0 (F _ n ts _)  = iFn n (σς ts)
tD0 (TD _ n vs t) = iTD n vs (σ t)

tD1 :: Ext a -> D [] a a -> TM a (D S.Set a (TS S.Set a))
tD1 _ (TD x n vs t)         = pure (TD x n vs (σ t))
tD1 b (F _ n ts as) = do
    (as', s) <- tseq b mempty as
    s' <- mtsc s (aLs as') tsσ
    as''<- taseq (s'@*) as'
    pure (F tsσ (n$>tsσ) tsσ as'')
  where
    tsσ=σς ts

tseq :: Ext a -> Subst a -> ASeq a -> TM a (ASeq (TS S.Set a), Subst a)
tseq _ s (SL l [])     = do {a <- fsv l "A"; pure (SL (TS [a] [a]) [], s)}
tseq b s (SL l (a:as)) = do
    (a',s0) <- tae b s a
    (SL tϵ as', s1) <- tseq b s0 (SL l as)
    (t, s2) <- cat s1 (aL a') tϵ
    -- pure $ traceShow (traceCat a' as' (aL a') (s1@*tϵ) (s2@*t)) (SL t (a':as'), s2)
    pure (SL t (a':as'), s2)

traceCat :: A b -> [A b] -> TS [] a -> TS [] a -> TS [] a -> Doc ann
traceCat a as t0 t1 tRes = pretty a <+> ":" <+> pretty t0
    <#> hsep (pretty<$>as) <+> ":" <+> pretty t1
    <#> indent 4 (hsep(pretty<$>a:as) <+> ":" <+> pretty tRes)
    <> hardline

splitFromLeft :: Int -> [a] -> ([a], [a])
splitFromLeft n xs | nl <- length xs = splitAt (nl-n) xs

{-# SCC cat #-}
cat :: Subst a -> TS S.Set a -> TS S.Set a -> TM a (TS S.Set a, Subst a)
cat s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- usc LF s r0 l1 -- narrow supplied arguments
    pure (TS l0 r1, s')

  -- stack variables: at most one on left/right, occurs at the leftmost
  -- (check that user-supplied signatures obey this principle)

fr :: a -> T.Text -> TM a (Nm a)
fr l t = state (\(TSt m s) -> let n=m+1 in (Nm t (U n) l, TSt n s))

ftv, fsv :: a -> T.Text -> TM a (T S.Set a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)

-- invariants for our inverses: pops off atomic tags.
-- invariants for sum types: do not bring in stack variables (thus can be reversed)

exps :: a -> TS S.Set a -> TM a (TS S.Set a)
exps _ t@(TS (SV{}:_) _) = pure t; exps _ t@(TS _ (SV{}:_)) = pure t
exps x (TS l r) = do {ᴀ <- fsv x "A"; pure (TS (ᴀ:l) (ᴀ:r))}

tae :: Ext a -> Subst a -> A a -> TM a (A (TS S.Set a), Subst a)
tae _ s (B l Dip)      = do {a <- fsv l "A"; b <- ftv l "b"; c <- fsv l "c"; pure (B (TS [a, b, QT l (TS [a] [c])] [c,b]) Dip, s)}
tae _ s (B l Doll)     = do {a <- fsv l "A"; b <- fsv l "B"; pure (B (TS [a, QT l (TS [a] [b])] [b]) Doll, s)}
tae b s a = do
    (a',s') <- ta b s a
    let t=aL a'
    t' <- exps (aL a) t
    pure (a' {aL = t'}, s')

ta :: Ext a -> Subst a -> A a -> TM a (A (TS S.Set a), Subst a)
ta _ s (L l lit@I{})  = pure (L (TS [] [TP l Int]) lit, s)
ta _ s (L l lit@BL{}) = pure (L (TS [] [TP l Bool]) lit, s)
ta b s (V _ n)        = do {ts <- lA (fns b) n; pure (V ts (n$>ts), s)}
ta _ s (B l Un)       = do {n <- ftv l "a"; pure (B (TS [n] []) Un, s)}
ta _ s (B l Dup)      = do {n <- ftv l "a"; pure (B (TS [n] [n,n]) Dup, s)}
ta _ s (B l Swap)     = do {a <- ftv l "a"; b <- ftv l "b"; pure (B (TS [a,b] [b,a]) Swap, s)}
ta b s (Q l as)       = do {(as', s') <- tseq b s as; pure (Q (TS [] [QT l (aLs as')]) as', s')}
ta b s (Inv _ a)      = do {(a', s') <- ta b s a; let TS l r = aL a' in pure (Inv (TS r l) a', s')}
ta _ s (C l tt)       = let ts=TS [] [TT l tt] in pure (C ts (tt$>ts), s)
ta b s (Pat _ as)     = do
    (as', s0) <- tS b s (aas as)
    sigs <- traverse (fmap pare.(s0@*).aLs) as'
    let rights=trights<$>sigs; lefts=tlefts<$>sigs
    (pRight, s1) <- dU RF s0 rights; (pLeft, s2) <- dU RF s1 lefts
    let t=TS pLeft pRight
    pure (Pat t (SL t as'), s2)

pare :: TS f a -> TS f a
pare (TS (SV _ ᴀ:l) (SV _ ᴄ:r)) | ᴀ==ᴄ = TS l r; pare t=t

dU :: F -> Subst a -> [TSeq S.Set a] -> TM a (TSeq S.Set a, Subst a)
dU _ s [ts]       = pure (ts, s)
dU f s (t0:t1:ts) = do {(tϵ, s') <- usc f s t0 t1; dU f s' (tϵ:ts)}

tS :: Ext a -> Subst a -> [ASeq a] -> TM a ([ASeq (TS S.Set a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

onM :: Monad m => (b -> b -> m c) -> (a -> m b) -> a -> a -> m c
onM g f x y = do {x' <- f x; y' <- f y; g x' y'}

-- PROBLEM: when do we add the ⊕ ?
-- I think doing it in ua is too early. We want sequences of types to be ⊕ together...
