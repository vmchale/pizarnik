{-# LANGUAGE OverloadedStrings #-}

module Ty ( TE, Ext (..), tM ) where

import           A
import           Control.Monad.Except       (throwError)
import           Control.Monad.State.Strict (StateT, gets, modify, runStateT, state)
import           Data.Bifunctor             (first)
import           Data.Foldable              (traverse_)
import           Data.Function              (on)
import           Data.Functor               (($>))
import qualified Data.IntMap                as IM
import qualified Data.Text                  as T
import           Nm
import           Pr
import           Prettyprinter              (Doc, Pretty (pretty), hardline, hsep, indent, squotes, (<+>))
import           Ty.Clone

infixr 6 @>
infixl 6 @@
infixr 6 @*

data Ext a = Ext { fns :: IM.IntMap (TS a)
                 , tds :: IM.IntMap ([Nm a], T a)
                 }

instance Semigroup (Ext a) where (<>) (Ext f0 td0) (Ext f1 td1) = Ext (f0<>f1) (td0<>td1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty

data TE a = UF (T a) (T a) F | MF (T a) (T a) | Ind (TSeq a)
          | USF (TSeq a) (TSeq a) F | MSF (TSeq a) (TSeq a)

tLs :: TSeq a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty (UF t0 t1 _)    = tc t0 $ "Failed to unify" <+> squotes (pretty t0) <+> "with" <+> squotes (pretty t1)
    pretty (Ind ts)      = tsc ts $ "Stack variables are only permitted at the leftmost" <+> squotes (hsep(pretty<$>ts))
    pretty (USF ts0 ts1 _) = tsc ts0 $ "Failed to unify" <+> squotes (hsep (pretty<$>ts0)) <+> "with" <+> squotes (hsep (pretty<$>ts1))
    pretty (MF t0 t1)    = tc t0 $ "Failed to match" <+> squotes (pretty t0) <+> "against" <+> squotes (pretty t1)
    pretty (MSF ts0 ts1) = tsc ts0 $ "Failed to match" <+> hsep (pretty<$>ts0) <+> "against" <+> hsep (pretty<$>ts1)

tc t p = pretty (tL t) <> ":" <+> p
tsc t p = pretty (tLs t) <> ":" <+> p

instance Pretty a => Show (TE a) where show=show.pretty

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

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst tv sv) = Subst (f tv) sv; mapSV f (Subst tv sv) = Subst tv (f sv)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
ising n t = Subst IM.empty (IM.singleton (unU$un n) t)

iFn :: Nm a -> TS b -> TM b ()
iFn (Nm _ (U i) _) ts = modify (\(TSt m (Ext f c)) -> TSt m (Ext (IM.insert i ts f) c))

iTD :: Nm a -> [Nm b] -> T b -> TM b ()
iTD (Nm _ (U i) _) vs t = modify (\(TSt m (Ext f c)) -> TSt m (Ext f (IM.insert i (vs,t) c)))

(@*) :: Subst a -> TS a -> TS a
s @* (TS l r) = TS (s@@l) (s@@r)

{-# SCC (@@) #-}
(@@) :: Subst a -> TSeq a -> TSeq a
(@@) _ []          = []
(@@) s (SV _ n:ts) = s@~>n++s@@ts
(@@) s (t:ts)      = (s@>t):s@@ts

(@~>) :: Subst a -> Nm a -> TSeq a
(@~>) s v@(Nm _ (U i) x) =
    case IM.lookup i (svs s) of
        Just ts -> mapSV (IM.delete i) s @@ ts
        Nothing -> [SV x v]

{-# SCC (@>) #-}
(@>) :: Subst a -> T a -> T a
(@>) _ t@TP{}          = t
(@>) _ t@TT{}          = t
(@>) s (TA x t0 t1)    = TA x (s@>t0) (s@>t1)
(@>) s (QT x (TS l r)) = QT x (TS (s@@l) (s@@r))
(@>) s (TI x t)        = TI x (s@>t)
(@>) s t@(TV _ n)      =
    let u=unU (un n) in
    case IM.lookup u (tvs s) of
        Nothing -> t
        Just t' -> mapTV (IM.delete u) s@>t'
(@>) s (Σ x ts) = Σ x ((s@@)<$>ts)
(@>) _ t@SV{} = error ("Internal error: (@>) applied to stack variable " ++ show t)

{-# SCC usc #-}
usc :: F -> Subst a -> TSeq a -> TSeq a -> TM a (TSeq a, Subst a)
usc f s = uas f s `on` (s@@)

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
uac f s = ua f s `on` (s@>)

{-# SCC ua #-}
ua :: F -> Subst a -> T a -> T a -> TM a (T a, Subst a)
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
ua LF s t0@(TT x _) t1@(TT _ _) = pure (Σ x [[t0],[t1]], s) -- TODO: tseq... unifies different length sequences as well!

mSig :: TS a -> TS a -> TM a (Subst a)
mSig (TS l0 r0) (TS l1 r1) = do {s <- ms l0 l1; msc s r0 r1}

msc :: Subst a -> TSeq a -> TSeq a -> TM a (Subst a)
msc s = ms `on` (s@@)

-- FIXME: 54:26: Failed to match 'C 'B a against 'B x
ms :: TSeq a -> TSeq a -> TM a (Subst a)
ms t0e@(SV{}:t0) t1e@((SV _ sn1):t1) =
    let n0=length t0; n1=length t1 in
    case compare n0 n1 of
        GT -> throwError $ MSF t0e t1e
        _ -> let (uws, res) = splitFromLeft n0 t1
             in msc (ising sn1 uws) t0 res
ms t0e@(SV _ v0:t0) t1 =
    let n0=length t0; n1=length t1
    in if n0>n1 then throwError $ MSF t0e t1 else let (uws, res) = splitFromLeft n0 t1 in msc (ising v0 uws) t0 res
ms (t0:ts0) (t1:ts1) = do {s' <- ma t0 t1; msc s' ts0 ts1}
ms [] [] = pure mempty
ms ts0 [] = throwError$ MSF ts0 []
ms [] ts1 = throwError$ MSF ts1 []

{-# SCC ma #-}
ma :: T a -> T a -> TM a (Subst a)
ma (TP _ p0) (TP _ p1) | p0==p1 = pure mempty
ma (TT _ n0) (TT _ n1) | n0==n1 = pure mempty
ma (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
ma (TV _ n0) t = pure (Subst (IM.singleton (unU$un n0) t) IM.empty)
ma (QT _ ts0) (QT _ ts1) = mSig ts0 ts1
ma t0@QT{} t1 = throwError $ MF t0 t1

mtsc :: Subst a -> TS a -> TS a -> TM a (Subst a)
mtsc s asig = mSig (s@*asig)

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
    let as''=faseq (s'@*) as'
    pure (F ts (n$>ts) ts as'')

tseq :: Ext a -> Subst a -> ASeq a -> TM a (ASeq (TS a), Subst a)
tseq _ s (SL l [])     = do {a <- fsv l "A"; pure (SL (TS [a] [a]) [], s)}
tseq b s (SL l (a:as)) = do
    (a',s0) <- tae b s a
    (SL tϵ as', s1) <- tseq b s0 (SL l as)
    (t, s2) <- cat s1 (aL a') tϵ
    -- pure $ traceShow (traceCat a' as' (aL a') (s1@*tϵ) (s2@*t)) (SL t (a':as'), s2)
    pure (SL t (a':as'), s2)

traceCat :: A b -> [A b] -> TS a -> TS a -> TS a -> Doc ann
traceCat a as t0 t1 tRes = pretty a <+> ":" <+> pretty t0
    <#> hsep (pretty<$>as) <+> ":" <+> pretty t1
    <#> indent 4 (hsep(pretty<$>a:as) <+> ":" <+> pretty tRes)
    <> hardline

splitFromLeft :: Int -> [a] -> ([a], [a])
splitFromLeft n xs | nl <- length xs = splitAt (nl-n) xs

{-# SCC cat #-}
-- we can only generalize a to a⊕b on the right, i.e. r0
-- (pass focus to ua while stitching)
cat :: Subst a -> TS a -> TS a -> TM a (TS a, Subst a)
cat s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- usc LF s r0 l1 -- narrow supplied arguments (NE where list is expected)
    pure (TS l0 r1, s')

  -- stack variables: at most one on left/right, occurs at the leftmost
  -- (check that user-supplied signatures obey this principle)

fr :: a -> T.Text -> TM a (Nm a)
fr l t = state (\(TSt m s) -> let n=m+1 in (Nm t (U n) l, TSt n s))

ftv, fsv :: a -> T.Text -> TM a (T a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)

-- invariants for our inverses: pops off atomic tags.
-- invariants for sum types: do not bring in stack variables (thus can be reversed)

exps :: a -> TS a -> TM a (TS a)
exps _ t@(TS (SV{}:_) _) = pure t; exps _ t@(TS _ (SV{}:_)) = pure t
exps x (TS l r) = do {ᴀ <- fsv x "A"; pure (TS (ᴀ:l) (ᴀ:r))}

tae :: Ext a -> Subst a -> A a -> TM a (A (TS a), Subst a)
tae _ s (B l Dip)      = do {a <- fsv l "A"; b <- ftv l "b"; c <- fsv l "c"; pure (B (TS [a, b, QT l (TS [a] [c])] [c,b]) Dip, s)}
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
    (as', s') <- tS b s (aas as)
    let sigs=aLs<$>as'
        rights=trights<$>sigs; lefts=tlefts<$>sigs
    (pRight, s'') <- succUnify RF s' rights
    (pLeft, s''') <- succUnify LF s'' lefts
    let t=TS pLeft pRight
    pure (Pat t (SL t as'), s''') -- unify rs, unify with different focus (left, `true & `false -> `true ⊕ `false

succUnify :: F -> Subst a -> [TSeq a] -> TM a (TSeq a, Subst a)
succUnify _ s [ts]       = pure (ts, s)
succUnify f s (t0:t1:ts) = do {(tϵ, s') <- usc f s t0 t1; succUnify f s' (tϵ:ts)}

tS :: Ext a -> Subst a -> [ASeq a] -> TM a ([ASeq (TS a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

-- PROBLEM: when do we add the ⊕ ?
-- I think doing it in ua is too early. We want sequences of types to be ⊕ together...
