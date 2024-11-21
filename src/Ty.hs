{-# LANGUAGE OverloadedStrings #-}

module Ty ( TE, Ext (..), tM ) where

import           A
import           B
import           Control.Composition              ((&:))
import           Control.Exception                (Exception)
import           Control.Monad                    (foldM, unless)
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.State.Strict (StateT, gets, modify, runStateT, state)
import           Data.Bifunctor                   (first, second)
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import           Data.List                        (unsnoc)
import qualified Data.Text                        as T
import           Data.Typeable                    (Typeable)
import           Nm
import           Nm.Map                           (NmMap)
import qualified Nm.Map                           as Nm
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), hardline, hsep, indent, (<+>))
import           Ty.Clone

infixl 7 \-
infixr 6 @>
infixl 6 @@
infixr 6 @*

data Ext a = Ext { fns :: IM.IntMap (TS a), tds :: Cs a }

instance Semigroup (Ext a) where (<>) (Ext f0 td0) (Ext f1 td1) = Ext (f0<>f1) (td0<>td1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty

data TE a = UF (T a) (T a) F | MF (T a) (T a) F
          | USF (TSeq a) (TSeq a) F | MSF (TSeq a) (TSeq a) F | BE (BE a)
          | PM (TSeq a)

tLs :: TSeq a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty (UF t0 t1 f)    = tc t0 f $ "Failed to unify" <+> sq (pretty t0) <+> "with" <+> sq (pretty t1)
    pretty (USF ts0 ts1 f) = tsc ts0 f $ "Failed to unify" <+> sq (pSeq ts0) <+> "with" <+> sq (pSeq ts1)
    pretty (MF t0 t1 f)    = tc t0 f $ "Failed to match" <+> sq (pretty t0) <+> "against" <+> sq (pretty t1)
    pretty (MSF ts0 ts1 f) = tsc ts0 f $ "Failed to match" <+> sq (pSeq ts0) <+> "against" <+> sq (pSeq ts1)
    pretty (BE e)          = pretty e
    pretty (PM ts)         = pretty (tLs ts) <> ":" <+> "Pattern match arms must begin with an inverse constructor."

tc t f p = pretty (tL t) <> ":" <+> pretty f <+> p
tsc t f p = pretty (tLs t) <> ":" <+> pretty f <+> p

instance Pretty a => Show (TE a) where show=show.pretty

instance (Typeable a, Pretty a) => Exception (TE a) where

data F = LF | RF

instance Pretty F where pretty LF="⦠"; pretty RF="∢"

instance Show F where show=show.pretty

data TSt a = TSt { maxT :: !Int, lo :: !(Ext a) }

type TM x = StateT (TSt x) (Either (TE x))

runTM :: Int -> TM a b -> Either (TE a) (b, Ext a, Int)
runTM u = fmap (\(x, TSt m st) -> (x, st, m)).flip runStateT (TSt u (Ext IM.empty IM.empty))

type Bt a = IM.IntMap (T a)
data Subst a = Subst { tvs :: Bt a, svs :: IM.IntMap (TSeq a) }

instance Pretty (Subst a) where pretty (Subst t s) = "tv" <#> pBound t <##> "sv" <#> pBound s

instance Show (Subst a) where show=show.pretty

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst tv sv) = Subst (f tv) sv; mapSV f (Subst tv sv) = Subst tv (f sv)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
sTV n t = Subst (IM.singleton (unU$un n) t) IM.empty

(\-) s u = mapTV (IM.delete u) s

tCtx :: Cs a -> T a -> Either (BE a) (T a)
tCtx c t@TC{} = uncurry (β c) (tun t)
tCtx c t@TA{} = uncurry (β c) (tun t)
tCtx _ t      = Right t

tun :: T a -> (Nm a, [T a])
tun (TC _ n)     = (n, [])
tun (TA _ t0 t1) = second (++[t1]) (tun t0)

lΒ :: Cs a -> T a -> TM a (T a)
lΒ c = liftEither . first BE . tCtx c

iFn :: Nm a -> TS b -> TM b ()
iFn (Nm _ (U i) _) ts = modify (\(TSt m (Ext f c)) -> TSt m (Ext (IM.insert i ts f) c))

iTD :: Nm a -> [Nm b] -> T b -> TM b ()
iTD (Nm _ (U i) _) vs t = modify (\(TSt m (Ext f c)) -> TSt m (Ext f (IM.insert i (vs,t) c)))

{-# SCC (@*) #-}
(@*) :: Subst a -> TS a -> TM a (TS a)
s @* (TS l r) = TS <$> s@@l <*> s@@r

{-# SCC peek #-}
peek :: Subst a -> TSeq a -> TM a (TSeq a)
peek _ []          = pure []
peek s (SV _ n:ts) = do {v <- s@~>n; pure (v++ts)}
peek s (t:ts)      = do {t' <- s@>t; pure (t':ts)}

peekS :: Subst a -> TS a -> TM a (TS a)
peekS s (TS l r) = TS <$> peek s l <*> peek s r

{-# SCC (@@) #-}
(@@) :: Subst a -> TSeq a -> TM a (TSeq a)
(@@) _ []          = pure []
(@@) s (SV _ n:ts) = do {v <- s@~>n; (v++)<$>s@@ts}
(@@) s (t:ts)      = do {t' <- s@>t; (t':)<$>s@@ts}

-- when does a US get concretized? (look at type annotations)

(@~>) :: Subst a -> Nm a -> TM a (TSeq a)
(@~>) s v@(Nm _ (U i) x) =
    case IM.lookup i (svs s) of
        Just ts -> mapSV (IM.delete i) s @@ ts
        Nothing -> pure [SV x v]

{-# SCC (@>) #-}
(@>) :: Subst a -> T a -> TM a (T a)
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
(@>) s t@(TV _ (Nm _ (U u) _)) =
    case IM.lookup u (tvs s) of
        Nothing -> pure t
        Just t' -> s\-u@>t'
(@>) s (Σ x ts) = Σ x <$> traverse (s@@) ts
(@>) _ SV{} = error "Internal error: (@>) applied to stack variable "

{-# SCC usc #-}
usc :: F -> Subst a -> TSeq a -> TSeq a -> TM a (TSeq a, Subst a)
usc f s = uas f s `onM` peek s

φ :: TSeq a -> TSeq a
φ ts = case unsnoc ts of {Just (tsϵ, Σ l as) -> [Σ l ((tsϵ++)<$>as)]; Just (ts', t) -> φ ts'++[t]; Nothing -> []}

{-# SCC uas #-}
uas :: F -> Subst a -> TSeq a -> TSeq a -> TM a (TSeq a, Subst a)
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
uas f s (t0:ts0) (t1:ts1) = do
    (tϵ, s') <- ua f s t0 t1
    first (tϵ:) <$> usc f s' ts0 ts1
uas f _ t0 [] = throwError $ USF t0 [] f
uas f _ [] t1 = throwError $ USF t1 [] f

{-# SCC uac #-}
uac :: F -> Subst a -> T a -> T a -> TM a (T a, Subst a)
uac f s = ua f s `onM` (s@>)

{-# SCC ua #-}
ua :: F -> Subst a -> T a -> T a -> TM a (T a, Subst a)
ua _ s t@(TP _ p0) (TP _ p1) | p0==p1 = pure (t, s)
ua LF _ t0@TP{} t1@TP{} = throwError $ UF t0 t1 LF
ua _ s t@(TV _ n0) (TV _ n1) | n0 == n1 = pure (t, s)
ua _ s t0 (TV _ n) = pure (t0, iTV n t0 s)
ua _ s (TV _ n) t1 = pure (t1, iTV n t1 s) -- c unifies with `nothing on the right but could be c = `nothing ⊕ ... hm
ua f s (TA x t0 t1) (TA _ t0' t1') = do
    (t0ϵ, s0) <- ua f s t0 t0'
    (t1ϵ, s1) <- uac f s0 t1 t1'
    pure (TA x t0ϵ t1ϵ, s1)
ua _ s (QT x t0) (QT _ t1) = first (QT x) <$> us s t0 t1
ua _ s t0@(TT _ tt0) (TT _ tt1) | tt0 == tt1 = pure (t0, s)
ua RF s (TT x n0) (TT _ n1) = pure (Σ x (Nm.fromList [(n0,[]),(n1,[])]), s)
ua LF _ t0@TT{} t1@TT{} = throwError $ UF t0 t1 LF
ua RF s (Σ _ ts) (TT x n1) = pure (Σ x (Nm.insert n1 [] ts), s)
ua RF s (TT x n1) (Σ _ ts) = pure (Σ x (Nm.insert n1 [] ts), s)
ua RF s (Σ x0 σ0) (Σ _ σ1) = pure (Σ x0 (σ0<>σ1), s)

mSig :: TS a -> TS a -> TM a (Subst a)
mSig (TS l0 r0) (TS l1 r1) = do {s <- ms RF mempty r0 r1; msc LF s l0 l1}

msc :: F -> Subst a -> TSeq a -> TSeq a -> TM a (Subst a)
msc f s = ms f s `onM` peek s

ms :: F -> Subst a -> TSeq a -> TSeq a -> TM a (Subst a)
ms f s t0e@(SV{}:t0) t1e@((SV _ sn1):t1) =
    let n0=length t0; n1=length t1 in
    if n0>n1
        then throwError $ MSF t0e t1e f
        else let (uws, res) = splitFromLeft n0 t1
             in msc f (iSV sn1 uws s) t0 res
ms f s t0e@(SV _ v0:t0) t1 = do
    cs <- gets (tds.lo)
    t1ϵ <- traverse (lΒ cs) t1
    let n0=length t0; n1=length t1ϵ
    if n0>n1
        then throwError $ MSF t0e t1ϵ f
        else let (uws, res) = splitFromLeft n0 t1ϵ
             in msc f (iSV v0 uws s) t0 res
ms f s (t0:ts0) (t1:ts1) = do {s' <- ma f t0 t1; msc f (s<>s') ts0 ts1}
ms _ s [] [] = pure s
ms f _ ts0 [] = throwError$ MSF ts0 [] f
ms f _ [] ts1 = throwError$ MSF ts1 [] f

mσ f s σ0 σ1 =
    let (t0s,t1s)=unzip (Nm.elems$Nm.intersectionWith (,) σ0 σ1)
    in mss s t0s t1s
  where
    mss sϵ [] []         = pure sϵ
    mss sϵ (x:xs) (y:ys) = do {s' <- msc f sϵ x y; mss s' xs ys}

{-# SCC ma #-}
ma :: F -> T a -> T a -> TM a (Subst a)
ma _ (TP _ p0) (TP _ p1) | p0==p1 = pure mempty
ma _ (TT _ n0) (TT _ n1) | n0==n1 = pure mempty
ma _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
ma _ (TV _ n0) t = pure (sTV n0 t)
ma f t0 t1@TV{} = throwError $ MF t0 t1 f
ma _ (QT _ ts0) (QT _ ts1) = mSig ts0 ts1
ma f t0@QT{} t1 = throwError $ MF t0 t1 f
-- on the left: type annotation must be narrower than what it accepts
-- on the right: type annotation can be more general
ma LF t0@(Σ _ σ0) t1@(Σ _ σ1) = do
    unless (σ1 `Nm.isSubmapOf` σ0)
        (throwError $ MF t0 t1 LF) *> mσ LF mempty σ0 σ1
ma RF t0@(Σ _ σ0) t1@(Σ _ σ1) = do
    unless (σ0 `Nm.isSubmapOf` σ1)
        (throwError $ MF t0 t1 RF) *> mσ RF mempty σ0 σ1
ma LF t0@(Σ _ σ) t1@(TT _ n) =
    unless (n `Nm.member` σ)
        (throwError $ MF t0 t1 LF) $> mempty
ma RF t0@(TT _ n) t1@(Σ _ σ) =
    unless (n `Nm.member` σ)
        (throwError $ MF t0 t1 RF) $> mempty
ma RF t0@Σ{} t1@TT{} = throwError $ MF t0 t1 RF
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

mtsc :: Subst a -> TS a -> TS a -> TM a (Subst a)
mtsc s asig tsig = do {asig' <- s@*asig; cs <- gets (tds.lo); tsig' <- ʙ cs tsig; mSig asig' (𝜙 tsig')}
  where 𝜙 (TS l r) = (TS&:φ) l r
        ʙ st (TS l r) = TS <$> traverse (lΒ st) l <*> traverse (lΒ st) r

us :: Subst a -> TS a -> TS a -> TM a (TS a, Subst a)
us s (TS l0 r0) (TS l1 r1) = do {(l,s') <- usc LF s l0 l1; (r,s'') <- usc RF s' r0 r1; pure (TS l r, s'')}

liftClone :: TS a -> TM a (TS a)
liftClone ts = do {u <- gets maxT; let (w, ts') = cloneSig u ts in modify (\s -> s {maxT = w}) $> ts'}

lA :: IM.IntMap (TS a) -> Nm a -> TM a (TS a)
lA es (Nm _ (U i) _) = do
    b <- gets (fns.lo)
    case IM.lookup i b of
        Just ts -> liftClone ts
        Nothing -> case IM.lookup i es of
            Just ts -> liftClone ts
            Nothing -> pure $ IM.findWithDefault (error "Internal error. Name lookup failed during type resolution.") i es

tM :: Int -> Ext a -> M a a -> Either (TE a) (M a (TS a), Ext a, Int)
tM i ex = runTM i.tMM ex

tMM :: Ext a -> M a a -> TM a (M a (TS a))
tMM b (M is ds) = M is <$> tD b ds

tD :: Ext a -> [D a a] -> TM a [D a (TS a)]
tD b ds = traverse_ tD0 ds *> traverse (tD1 b) ds

tD0 :: D a a -> TM a ()
tD0 (F _ n ts _)  = iFn n ts
tD0 (TD _ n vs t) = iTD n vs t

tD1 :: Ext a -> D a a -> TM a (D a (TS a))
tD1 _ (TD x n vs t)         = pure (TD x n vs t)
tD1 b (F _ n ts as) = do
    (as', s) <- tseq b mempty as
    s' <- mtsc s (aLs as') ts
    as''<- taseq (s'@*) as'
    pure (F ts (n$>ts) ts as'')

tseq :: Ext a -> Subst a -> ASeq a -> TM a (ASeq (TS a), Subst a)
tseq _ s (SL l [])     = do {a <- fsv l "A"; pure (SL (TS [a] [a]) [], s)}
tseq b s (SL l (a:as)) = do
    (a',s0) <- tae b s a
    (SL tϵ as', s1) <- tseq b s0 (SL l as)
    (t, s2) <- cat s1 (aL a') tϵ
    -- pure $ traceShow (traceCat a' as' (aL a') tϵ t) (SL t (a':as'), s2)
    pure (SL t (a':as'), s2)

traceCat :: A b -> [A b] -> TS a -> TS a -> TS a -> Doc ann
traceCat a as t0 t1 tRes = pretty a <+> ":" <+> pretty t0
    <#> hsep (pretty<$>as) <+> ":" <+> pretty t1
    <#> indent 4 (hsep(pretty<$>a:as) <+> ":" <+> pretty tRes)
    <> hardline

splitFromLeft :: Int -> [a] -> ([a], [a])
splitFromLeft n xs | nl <- length xs = splitAt (nl-n) xs

{-# SCC cat #-}
cat :: Subst a -> TS a -> TS a -> TM a (TS a, Subst a)
cat s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- usc LF s r0 l1 -- narrow supplied arguments
    pure (TS l0 r1, s')

  -- stack variables: at most one on left/right, occurs at the leftmost
  -- (check that user-supplied signatures obey this principle)

fr :: a -> T.Text -> TM a (Nm a)
fr l t = state (\(TSt m s) -> let n=m+1 in (Nm t (U n) l, TSt n s))
frc n = fr (loc n) (text n)

ftv, fsv :: a -> T.Text -> TM a (T a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)

-- invariants for our inverses: pops off atomic tags.
-- invariants for sum types: do not bring in stack variables (thus can be reversed)

exps :: a -> TS a -> TM a (TS a)
exps _ t@(TS (SV{}:_) _) = pure t; exps _ t@(TS _ (SV{}:_)) = pure t
exps x (TS l r) = do {ᴀ <- fsv x "A"; pure (TS (ᴀ:l) (ᴀ:r))}

tae :: Ext a -> Subst a -> A a -> TM a (A (TS a), Subst a)
tae _ s (B l Dip)      = do {a <- fsv l "A"; b <- ftv l "b"; c <- fsv l "C"; pure (B (TS [a, b, QT l (TS [a] [c])] [c,b]) Dip, s)}
tae _ s (B l Doll)     = do {a <- fsv l "A"; b <- fsv l "B"; pure (B (TS [a, QT l (TS [a] [b])] [b]) Doll, s)}
tae b s a = do
    (a',s') <- ta b s a
    let t=aL a'
    t' <- exps (aL a) t
    pure (a' {aL = t'}, s')

ta :: Ext a -> Subst a -> A a -> TM a (A (TS a), Subst a)
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
    sigs <- traverse (peekS s0.aLs) as'
    (t, s1) <- dU s0 sigs
    pure (Pat t (SL t as'), s1)

σs :: (a, NmMap (TSeq a)) -> TSeq a -> TM a (a, NmMap (TSeq a))
σs (x, ps) t = pure (x, Nm.insert undefined undefined ps)
σs _ t       = throwError (PM t)

dL :: [TSeq a] -> TM a (T a)
dL (t:ts) = uncurry Σ<$>foldM σs undefined ts

-- FIXME: lefts can fan-out within limits since it's an { x & y } expression, do those first and apply substitution (or generalization)?
-- right now the result is wrong b/c it tries to use substitutions on the right (equalities) rather than generalizations that can come from the lefts...
dU :: Subst a -> [TS a] -> TM a (TS a, Subst a)
dU s tss = do
    l' <- dL ls
    -- unify rights
    pure (TS [l'] undefined, undefined)
  where ls=map tlefts tss; rs=map trights tss

tS :: Ext a -> Subst a -> [ASeq a] -> TM a ([ASeq (TS a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

onM :: Monad m => (b -> b -> m c) -> (a -> m b) -> a -> a -> m c
onM g f x y = do {x' <- f x; y' <- f y; g x' y'}
