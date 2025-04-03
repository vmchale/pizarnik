{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module Ty ( TE, Ext (..), tM ) where

import           A
import           B
import           C
import           Control.Exception                (Exception)
import           Control.Monad                    (unless, when, zipWithM)
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.State.Strict (StateT, gets, modify, runStateT, state)
import           Data.Bifunctor                   (first, second)
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.IntSet                      as IS
import           Data.List                        (unsnoc)
import qualified Data.Set                         as S
import qualified Data.Text                        as T
import           Data.Typeable                    (Typeable)
import           Nm
import qualified Nm.Map                           as Nm
import qualified Nm.Set                           as NmSet
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), hardline, hsep, indent, (<+>))
import           Ty.Clone

infixl 7 \-
infixr 6 @>
infixl 6 @@
infixr 6 @*
infixr 7 @<>

type Ar = IM.IntMap Int

data Ext a = Ext { fns :: IM.IntMap (TS a), tds :: Cs a, arit :: Ar }

instance Semigroup (Ext a) where (<>) (Ext f0 td0 a0) (Ext f1 td1 a1) = Ext (f0<>f1) (td0<>td1) (a0<>a1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty (IM.fromList [(-1,0),(-2,0)])

data TE a = BE (BE a) | O (T a) (T a)
          | LE (TSeq a) (TSeq a)
          | Subsumesn't (T a) (T a)
          | PM (TSeq a) | AM (Nm a)

tLs :: TSeq a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty (LE ts0 ts1)        = tsc ts0$"length mismatch:" <+> sq (pretty ts0) <+> "and" <+> sq (pretty ts1)
    pretty (AM n)              = pretty (Nm.loc n) <> ":" <+> "tag of unknown arity:" <+> sq (pretty n)
    pretty (BE e)              = pretty e
    pretty (PM ts)             = pretty (tLs ts) <> ":" <+> "Pattern match arms must begin with an inverse constructor."
    pretty (O t₀ t₁)           = tc t₀$"occurs check failed: " <+> sq (pretty t₀) <> "," <+> sq (pretty t₁)
    pretty (Subsumesn't t0 t1) = tc t0$pretty t0 <+> "⊀" <+> pretty t1
    -- also ⊁

tc t p = pretty (tL t) <> ":" <+> p
tsc t p = pretty (tLs t) <> ":" <+> p

instance Pretty a => Show (TE a) where show=show.pretty

instance (Typeable a, Pretty a) => Exception (TE a) where

data F = LF | RF

instance Pretty F where pretty LF="⦠"; pretty RF="∢" -- "≬"

instance Show F where show=show.pretty

data TSt a = TSt { maxT :: !Int, lo :: !(Ext a) }

type TM x = StateT (TSt x) (Either (TE x))

runTM :: Int -> TM a b -> Either (TE a) (b, Ext a, Int)
runTM u = fmap (\(x, TSt m s) -> (x, s, m)).flip runStateT (TSt u (Ext IM.empty IM.empty (IM.fromList [(-1,0),(-2,0)])))

type Bt a = IM.IntMap (T a)
data Subst a = Subst { tvs :: Bt a, svs :: IM.IntMap (TSeq a) }

instance Pretty (Subst a) where pretty (Subst t s) = "tv" <#> pBound t <##> "sv" <#> pBound s

instance Show (Subst a) where show=show.pretty

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst v s) = Subst (f v) s; mapSV f (Subst v s) = Subst v (f s)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
sTV n t = Subst (IM.singleton (unU$un n) t) IM.empty

(\-) s u = mapTV (IM.delete u) s

sf :: T a -> T a -> TM a b
sf t0 t1 = throwError (Subsumesn't t0 t1)

tCtx :: Cs a -> T a -> Either (BE a) (T a)
tCtx c t | Just (n,s) <- tun t = β c n s | otherwise = Right t

-- Hutton §16.6
tun :: T a -> Maybe (Nm a, [T a])
tun = g [] where g s (TC _ n)     = Just (n, s)
                 g s (TA _ t0 t1) = g (t1:s) t0
                 g _ _            = Nothing

lΒ :: Cs a -> T a -> TM a (T a)
lΒ c = liftEither . first BE . tCtx c

iFn :: Nm a -> TS b -> TM b ()
iFn (Nm _ (U i) _) ts = modify (\(TSt m (Ext f c a)) -> TSt m (Ext (IM.insert i ts f) c a))

cA :: T a -> TM b ()
cA (Σ _ t) = modify (\(TSt m (Ext f c a)) -> TSt m (Ext f c (fmap length (Nm.xx t)<>a))); cA _=pure ()

iTD :: Nm a -> [Nm b] -> T b -> TM b ()
iTD (Nm _ (U i) _) vs t = modify (\(TSt m (Ext f c a)) -> TSt m (Ext f (IM.insert i (vs,t) c) a))

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

(@~>) :: Subst a -> Nm a -> TM a (TSeq a)
(@~>) s v@(Nm _ (U i) x) =
    case IM.lookup i (svs s) of
        Just ts -> mapSV (IM.delete i) s @@ ts
        Nothing -> pure [SV x v]

{-# SCC (@>) #-}
(@>) :: Subst a -> T a -> TM a (T a)
(@>) _ t@TP{}          = pure t
(@>) _ t@TT{}          = pure t
(@>) _ t@TC{}          = pure t
(@>) s (TA x t0 t1)    = TA x <$> s@>t0 <*> s@>t1
(@>) s (QT x sig)      = QT x<$>s@*sig
(@>) s (TI x t)        = TI x <$> s@>t
(@>) s t@(TV _ (Nm _ (U u) _)) =
    case IM.lookup u (tvs s) of
        Nothing -> pure t
        Just t' -> s\-u@>t'
(@>) s (Ρ l n@(Nm _ (U u) _) a r) =
    case IM.lookup u (tvs s) of
        -- FIXME: check for clashes if we substitute universal... move over to tag-section?
        -- use maxView on set to pick TVs
        Nothing -> Ρ l n <$> traverse (s@@) a <*> st (s@>) r
        Just t' -> s\-u@>t'
(@>) s (Σ x ts) = Σ x <$> traverse (s@@) ts
(@>) _ SV{} = error "Internal error: (@>) applied to stack variable "

st f = fmap S.fromList . traverse f . S.toList

occ :: T a -> IS.IntSet
occ (TV _ n)        = NmSet.singleton n
occ (TA _ t0 t1)    = occ t0<>occ t1
occ TP{}            = IS.empty
occ (TI _ t)        = occ t
occ (UU _ ts)       = occ@<>ts
occ (QT _ (TS l r)) = occ@<>l <> occ@<>r
occ TT{}            = IS.empty
occ TC{}            = IS.empty
occ SV{}            = IS.empty
occ (Σ _ a)         = foldMap (occ@<>) a
occ (Ρ _ n a s)     = NmSet.insert n$foldMap (occ@<>) a <> occ@<>S.toList s

-- "subsumes"
ϝ :: Cs a -> Subst a -> T a -> T a -> TM a (T a, Subst a)
ϝ _ s t@(TV _ n0) (TV _ n1) | n0==n1 = pure (t,s)
-- FIXME occurs check
ϝ _ s (TV _ n) t | n `NmSet.member` occ t = error"error message not yet implemented."
                 | otherwise = pure (t, iTV n t s)
ϝ _ s t (TV _ n) = pure (t, iTV n t s)
ϝ c s (QT x (TS l0 r0)) (QT _ (TS l1 r1)) = do
    -- contravariant
    (l',s₀) <- ϝs c s l1 l0
    (r',s₁) <- ϝs c s₀ r0 r1
    pure (QT x (TS l' r'), s₁)
ϝ _ _ t0 t1 = error (show (t0,t1))

ϝs=sv ϝ;ϝsc=ctx'ize ϝs

type UC v a = Cs a -> Subst a -> v -> v -> TM a (v, Subst a)

-- 𝜐 upsilon
sv :: UC (T a) a -> UC (TSeq a) a
sv _ _ s [] [] = pure ([], s)
sv u c s t0@(SV _ sn0:t0d) t1@(SV _ sn1:t1d) =
    let n0=length t0d; n1=length t1d in
    case compare n0 n1 of
        GT -> let (uws, res) = splitFromLeft n1 t0
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn1 uws s) t1d res
        _  -> let (uws, res) = splitFromLeft n0 t1
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn0 uws s) t0d res
sv u c s t0@(SV _ sn0:t0d) t1 =
    let n0=length t0d; n1=length t1 in
    case compare n0 n1 of
        GT -> throwError$LE t0 t1
        _  -> let (uws, res) = splitFromLeft n0 t1
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn0 uws s) t0d res
sv u c s t0 t1@(SV _ sn1:t1d) =
    let n0=length t0; n1=length t1d in
    case compare n0 n1 of
        LT -> throwError$LE t0 t1
        _  -> let (uws, res) = splitFromLeft n1 t0
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn1 uws s) t1d res
sv u c s (t0:ts0) (t1:ts1) = do
    (t',s') <- u c s t0 t1
    first (t':) <$> sv u c s' ts0 ts1
sv _ _ _ t0 [] = throwError$LE t0 []
sv _ _ _ [] t1 = throwError$LE [] t1

ctx'ize us c s = us c s `onM` peek s

-- ψ to pick apart RVs

nρ x n@(Nm t _ l) s a = do
    n' <- fr l t
    let t'=Ρ x n' s a
    pure (t', iTV n t')

-- fan out
φ :: Cs a -> Subst a -> T a -> T a -> TM a (T a, Subst a)
φ _ s t@(TT _ n0) (TT _ n1) | n0==n1 = pure (t,s)
φ _ s (TT x n0) (TT _ n1) = pure (Σ x (Nm.fromList [(n0,[]),(n1,[])]), s)
φ _ s (Σ _ as) (TT x n) = pure (Σ x (Nm.insert n [] as), s)
φ _ s (Σ x σ0) (Σ _ σ1) = pure (Σ x (σ0<>σ1), s)
φ _ s t@(TV _ n0) (TV _ n1) | n0==n1 = pure (t,s)
                            | otherwise = pure (t, iTV n1 t s)
φ _ _ (Ρ _ ρ σ a) t@TV{} = undefined
φ c s (Σ _ as) (Ρ x n σ a) = do
    (ς, s') <- φσ c s x σ as
    (n',g) <- nρ x n (σ<>as<>ς) a
    pure (n', g s')
φ _ s t@TP{} (Ρ x n σ a) = do
    (n',g) <- nρ x n σ (S.insert t a)
    pure (n',g s)
φ _ s t@TV{} (Ρ x n σ a) = do
    (n',g) <- nρ x n σ (S.insert t a)
    pure (n',g s)
φ _ s (TT _ tt) (Ρ x n σ a) =
    case Nm.lookup tt σ of
        Just (_:_) -> error "error message not implemented."
        _ -> do
            (n',g) <- nρ x n (Nm.insert tt [] σ) a
            pure (n',g s)

φσ c s l σ0 σ1 =
    φss s (Nm.toList l ς)
  where
    ς=Nm.intersectionWith (,) σ0 σ1

    φss sϵ []              = pure (Nm.empty, sϵ)
    φss sϵ ((n,(x,y)):xys) = do {(xy,s') <- φsc c sϵ x y; first (Nm.insert n xy) <$> (φss s' xys)}

φs=sv φ;φsc=ctx'ize φs

mσ c s σ0 σ1 =
    let (t0s,t1s)=unzip (Nm.elems$Nm.intersectionWith (,) σ0 σ1)
    in mss s t0s t1s
  where
    mss sϵ [] []         = pure sϵ
    mss sϵ (x:xs) (y:ys) = do {s' <- pvc lt c sϵ x y; mss s' xs ys}

pvc u c s = pv u c s `onM` peek s

pv :: (Cs a -> T a -> T a -> TM a (Subst a))
   -> Cs a -> Subst a -> TSeq a -> TSeq a -> TM a (Subst a)
pv u c s t0e@(SV{}:t0) t1e@(SV _ n:t1)
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in pvc u c (iSV n uws s) t0 res
    -- TODO: eat tags/constructors, β-expand
    | otherwise = throwError$LE t0e t1e
  where n0=length t0;n1=length t1
pv u c s t0e@(SV _ n:t0) t1
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in pvc u c (iSV n uws s) t0 res
    | otherwise = throwError$LE t0e t1
  where n0=length t0;n1=length t1
pv u c s (t0:t0s) (t1:t1s) = do {s' <- u c t0 t1; pvc u c (s<>s') t0s t1s}
pv _ _ _ [] [] = pure mempty
pv _ _ _ t0 [] = throwError$LE t0 []
pv _ _ _ [] t1 = throwError$LE [] t1

lt :: Cs a -> T a -> T a -> TM a (Subst a)
lt c t0@(Σ _ σ0) t1@(Σ _ σ1) = do
    unless (σ1 `Nm.isSubmapOf` σ0)
        (sf t0 t1) *> mσ c mempty σ0 σ1
lt _ t0@(Σ _ σ) t1@(TT _ n) =
    unless (n `Nm.member` σ)
        (sf t0 t1) $> mempty
lt _ (TT _ tt0) (TT _ tt1) | tt0==tt1 = pure mempty
lt _ t0@TT{} t1@Σ{} = sf t0 t1
lt _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
lt _ (TV _ n) t = pure (sTV n t)
lt c (QT _ ts0) (QT _ ts1) = mTS c ts1 ts0 -- TODO is this what we want to invert subsumption
lt c t0 t1 | Just (TC _ n0, a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = pv lt c mempty a0 a1
lt c t0 t1 | Just{} <- unA t0 = do {t0' <- βc c t0; lt c t0' t1}
lt c t0 t1 | Just{} <- unA t1 = do {t1' <- βc c t1; lt c t0 t1'}
lt _ t0 t1 = error (show (t0,t1))
-- can this be more lenient with stack variables? (a -- 'B,'A a -- 'C)
-- a (inferred) does not match 'A a (sig)? maybe it should idk

βc c t = do {cs <- gets (tds.lo); lΒ (c<>cs) t}

-- left: inferred can be more general than sig (propagate)
-- right: inferred must be narrower than sig
mTS :: Cs a -> TS a -> TS a -> TM a (Subst a)
mTS c (TS l0 r0) (TS l1 r1) = do {s <- pvc (\cϵ t0 t1 -> lt cϵ t1 t0) c mempty l0 l1; pv lt c s r0 r1 $> s}
-- FIXME: if we generalize on the right we should check it still matches on the left?

mtsc :: Cs a -> Subst a -> TS a -> TS a -> TM a (Subst a)
mtsc c s asig tsig = do {asig' <- s@*asig; mTS c asig' tsig}

liftClone :: TS a -> TM a (TS a)
liftClone ts = do {u <- gets maxT; let (w, ts') = cloneSig u ts in modify (\s -> s {maxT = w}) $> ts'}

lT :: Ar -> Nm a -> TM a Int
lT ex n@(Nm _ (U u) _) = do
    ars <- gets (arit.lo)
    case IM.lookup u ars of
        Just i  -> pure i
        Nothing -> case IM.lookup u ex of
            Just i  -> pure i
            Nothing -> throwError$AM n

lA :: IM.IntMap (TS a) -> Nm a -> TM a (TS a)
lA es (Nm _ (U i) _) = do
    b <- gets (fns.lo)
    case IM.lookup i b of
        Just ts -> liftClone ts
        Nothing -> case IM.lookup i es of
            Just ts -> liftClone ts
            Nothing -> error "Internal error. Name lookup failed during type resolution."

tM :: Int -> Ext a -> M a a -> Either (TE a) (M a (TS a), Ext a, Int)
tM i ex = runTM i.tMM ex

tMM :: Ext a -> M a a -> TM a (M a (TS a))
tMM b (M is ds) = M is <$> tD b ds

tD :: Ext a -> [D a a] -> TM a [D a (TS a)]
tD b ds = traverse_ tD0 ds *> traverse (tD1 b) ds

{-# SCC tD0 #-}
tD0 :: D a a -> TM a ()
tD0 (F _ n ts _)  = iFn n ts
tD0 (TD _ n vs t) = iTD n vs t *> cA t

{-# SCC tD1 #-}
tD1 :: Ext a -> D a a -> TM a (D a (TS a))
tD1 _ (TD x n vs t)         = pure (TD x n vs t)
tD1 b@(Ext _ c _) (F _ n ts as) = do
    (as', s) <- tseq b mempty as
    s' <- mtsc c s (aLs as') ts
    as''<- taseq (s'@*) as'
    pure (F ts (n$>ts) ts as'')

tseq :: Ext a -> Subst a -> ASeq a -> TM a (ASeq (TS a), Subst a)
tseq _ s (SL l [])     = do {a <- fsv l "A"; pure (SL (TS [a] [a]) [], s)}
tseq b s (SL l (a:as)) = do
    (a',s0) <- tae b s a
    (SL tϵ as', s1) <- tseq b s0 (SL l as)
    (t, s2) <- cat (tds b) s1 (aL a') tϵ
    -- pure $ traceShow (traceCat a' as' (aL a') tϵ t) (SL t (a':as'), s2)
    pure (SL t (a':as'), s2)

traceCat :: A b -> [A b] -> TS a -> TS a -> TS a -> Doc ann
traceCat a as t0 t1 tRes = pretty a <+> ":" <+> pretty t0
    <#> hsep (pretty<$>as) <+> ":" <+> pretty t1
    <#> indent 4 (hsep(pretty<$>a:as) <+> ":" <+> pretty tRes)
    <> hardline

(/|) :: [a] -> Int -> ([a], [a])
xs /| n = splitFromLeft n xs

splitFromLeft :: Int -> [a] -> ([a], [a])
splitFromLeft n xs | nl <- length xs = splitAt (nl-n) xs

{-# SCC cat #-}
cat :: Cs a -> Subst a -> TS a -> TS a -> TM a (TS a, Subst a)
cat c s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- ϝsc c s r0 l1
    pure (TS l0 r1, s')

  -- stack variables: at most one on left/right, occurs at the leftmost
  -- (check that user-supplied signatures obey this principle)

fr :: a -> T.Text -> TM a (Nm a)
fr l t = state (\(TSt m s) -> let n=m+1 in (Nm t (U n) l, TSt n s))

ftv, fsv, erv :: a -> T.Text -> TM a (T a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)
erv l n = Ρ l <$> fr l n <*> pure Nm.empty <*> pure S.empty

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
ta b s (V _ n)        = do {ts <- lA (fns b) n; pure (V ts (n$>ts), s)}
ta _ s (B l Un)       = do {n <- ftv l "a"; pure (B (TS [n] []) Un, s)}
ta _ s (B l Dup)      = do {n <- ftv l "a"; pure (B (TS [n] [n,n]) Dup, s)}
ta _ s (B l Swap)     = do {a <- ftv l "a"; b <- ftv l "b"; pure (B (TS [a,b] [b,a]) Swap, s)}
ta b s (Q l as)       = do {(as', s') <- tseq b s as; pure (Q (TS [] [QT l (aLs as')]) as', s')}
ta b s (Inv _ a)      = do {(a', s') <- ta b s a; let TS l r = aL a' in pure (Inv (TS r l) a', s')}
ta b s (C l tt)       = do
    p <- lT (arit b) tt
    -- TODO: pad beginning inverse constructors with ρ₀ etc. not a₀?
    ρ <- pad l p
    let ts=TS ρ (ρ++[TT l tt]) in pure (C ts (tt$>ts), s)
ta b s (Pat _ as)     = do
    (as', s0) <- tS b s (aas as)
    sigs <- traverse (peekS s0.aLs) as'
    (t, s1) <- dU (tds b) (arit b) s0 sigs
    pure (Pat t (SL t as'), s1)

an :: Ar -> [(Nm a, [T a])] -> TM a (T a, [[T a]])
an ar as = do
    (tas, tss) <- unzip<$>traverse (\(nm,ts) -> do{n<-lT ar nm; when (n>length ts) undefined $> (ts /| n)}) as
    pure (Σ l (Nm.fromList (zip nms tss)), tas)
  where l=loc (fst$head as); nms=map fst as

pad :: a -> Int -> TM a (TSeq a)
pad l n = traverse (\i -> erv l ("ρ"<>pᵤ i)) [1..n]

{-# SCC dU #-}
dU :: Cs a -> Ar -> Subst a -> [TS a] -> TM a (TS a, Subst a)
dU c e s tss = do
    ρ <- zipWithM pad (tLs<$>ls) [ rm-length r | r <- rs ]
    let ls'=zipWith (++) ρ ls; rs'=zipWith (++) ρ rs
    al <- traverse ai ls'
    (σ,ul) <- an e (concat al)
    (l',s') <- urs s ul; (r',s'') <- urs s' rs'
    (,s'') <$> exps (tLs$head ls) (TS (l'++[σ]) r')
  where tss'=map pare tss
        ls=map tlefts tss'; rs=map trights tss'
        rm=maximum (length<$>rs)

        urs sϵ [t]    = pure (t, sϵ)
        urs sϵ (t:ts) = do {(tr,s0) <- urs sϵ ts; φsc c s0 tr t}

        pare :: TS a -> TS a
        pare (TS (SV _ ᴀ:l) (SV _ ᴄ:r)) | ᴀ==ᴄ = TS l r; pare t=t

        ai :: [T a] -> TM a [(Nm a, [T a])]
        ai ts | Just (tsϵ, TT _ n) <- unsnoc ts = pure [(n, tsϵ)]
              | Just (tsϵ, Σ l as) <- unsnoc ts = pure $ second (++tsϵ) <$> Nm.toList l as
              | otherwise = throwError (PM ts)

tS :: Ext a -> Subst a -> [ASeq a] -> TM a ([ASeq (TS a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

onM :: Monad m => (b -> b -> m c) -> (a -> m b) -> a -> a -> m c
onM g f x y = do {x' <- f x; y' <- f y; g x' y'}

(@<>) :: (Monoid m, Foldable f) => (a -> m) -> f a -> m
(@<>) = foldMap
