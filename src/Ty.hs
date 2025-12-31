{-# LANGUAGE TupleSections #-}

module Ty ( TE, Ext (..), tM, tAS ) where

import           A
import           B
import           C
import           Control.Monad                    (foldM, when)
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.State.Strict (StateT (StateT), execStateT, get, modify, put, runStateT, state)
import           D
import           Data.Bifunctor                   (first, second)
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.IntSet                      as IS
import           Data.List                        (foldl')
import qualified Data.Text                        as T
import           F
import           G
import           Nm
import qualified Nm.Map                           as Nm
import qualified Nm.Set                           as NmSet
import           Pr
import           Prettyprinter                    (Pretty (pretty), (<+>))
import           Q
import           Ty.A

infixl 7 \-
infixr 6 @>
infixl 6 @@
infixr 6 @*

data Nt a = Nt { tβ :: Cs a, ars :: Ar }
π (Ext _ c r) = Nt c r

data Ext a = Ext { fns :: IM.IntMap (TS a), tds :: Cs a, arit :: Ar }

instance Semigroup (Ext a) where (<>) (Ext f0 td0 a0) (Ext f1 td1 a1) = Ext (f0<>f1) (td0<>td1) (a0<>a1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty (IM.fromDistinctAscList [(-2,0),(-1,0)])

data TE a = BE (BE a) | O (T a) (T a) | Os (Nm a) (TSeq a)
          | PM (TSeq a)
          | LE (TSeq a) (TSeq a)
          | LF (T a) (T a) | ΦF (T a) (T a) | CF (T a) (T a)
          | UF (T a) (T a) | MF (T a) (T a) | Bare (T a)
          | AM (Nm a) | IS (Nm a)
          deriving Functor

instance PT (TE a) where
    pp (UF t₀ t₁) = UF <$> pp t₀ <*> pp t₁; pp (O t₀ t₁) = O <$> pp t₀ <*> pp t₁
    pp (Os n ts)  = Os <$> psv n <*> traverse pp ts
    pp (LE ts₀ ts₁) = LE <$> traverse pp ts₀ <*> traverse pp ts₁
    pp (LF t₀ t₁) = LF <$> pp t₀ <*> pp t₁; pp (ΦF t₀ t₁) = ΦF <$> pp t₀ <*> pp t₁
    pp (CF t₀ t₁) = CF <$> pp t₀ <*> pp t₁; pp (MF t₀ t₁) = MF <$> pp t₀ <*> pp t₁
    pp e@AM{} = pure e; pp e@IS{} = pure e
    pp e@Bare{} = pure e; pp e@PM{} = pure e
    pp e@BE{} = pure e

tLs :: TSeq a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty=p0.ppt where
        p0 (LE ts0 ts1) = tsc ts0$"length mismatch:" <+> sq ts0 <+> "and" <+> sq ts1
        p0 (AM n)       = tn n$"unknown arity:" <+> sq n
        p0 (BE e)       = pretty e
        p0 (PM ts)      = tsc ts ":" <+> "Pattern match arms must begin with an inverse constructor."
        p0 (O t₀ t₁)    = tc t₀$"occurs check failed:" <+> sq t₀ <> "," <+> sq t₁
        p0 (Os n t)     = tn n$"occurs check failed:" <+> sq n <> "," <+> sqs t
        p0 (LF t0 t1)   = tc t0$pretty t0 <+> "⊀" <+> pretty t1
        p0 (ΦF t0 t1)   = tc t0$sq t0 <+> "not compatible with" <+> sq t1
        p0 (CF t0 t1)   = tc t0$sq t0 <+> "is not an acceptable argument, expected" <+> sq t1
        p0 (UF t0 t1)   = tc t0$"failed to unify" <+> sq t0 <+> "with" <+> sq t1
        p0 (MF t0 t1)   = tc t1$"could not match" <+> sq t0 <+> "against" <+> sq t1
        p0 (IS n)       = tn n (sq n <+> "not in scope.")
        p0 (Bare t)     = tc t$"Bare union:" <+> sq t

tn n p = pretty (Nm.loc n) <> ":" <+> p
tc t p = pretty (tL t) <> ":" <+> p
tsc t p = pretty (tLs t) <> ":" <+> p

data TSt a = TSt !Int !(Ext a)

type TM x = StateT (TSt x) (Either (TE x))
type UM x = StateT Int (Either (TE x))

liftTM :: TM a b -> UM a (b, Ext a)
liftTM x = StateT $ \u -> do {(y, TSt u' c) <- runStateT x (TSt u (Ext IM.empty IM.empty (IM.fromDistinctAscList [(-2,0),(-1,0)]))); Right ((y,c),u')}

type Bt a = IM.IntMap (T a)
data Subst a = Subst { tvs :: Bt a, svs :: IM.IntMap (TSeq a) }

instance Pretty (Subst a) where pretty (Subst t s) = "tv" <#> pBound t <##> "sv" <#> pBound s

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst v s) = Subst (f v) s; mapSV f (Subst v s) = Subst v (f s)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
sTV (Nm _ (U u) _) t = Subst (IM.singleton u t) IM.empty

(\-) s u = mapTV (IM.delete u) s

c1 :: Nm a -> T a -> T a -> UM a (Subst a)
c1 (Nm _ (U u) _) t te | u `IS.member` occ t = throwError $ O te t
                       | otherwise = pure (Subst (IM.singleton u t) IM.empty)

ci :: Nm a -> T a -> T a -> Subst a -> UM a (Subst a)
ci (Nm _ (U u) _) t te s | u `IS.member` occ t = throwError $ O te t
                         | otherwise = pure (mapTV (IM.insert u t) s)

cf, sf, φf :: T a -> T a -> UM a b
sf t0 t1 = throwError$LF t0 t1
φf t0 t1 = throwError$ΦF t0 t1; cf t0 t1 = throwError$CF t0 t1

-- Hutton §16.6
tun :: T a -> Maybe (Nm a, [T a])
tun = g [] where g s (TC _ n)     = Just (n, s)
                 g s (TA _ t0 t1) = g (t1:s) t0
                 g _ _            = Nothing

lΒ :: Cs a -> T a -> UM a (T a)
lΒ cϵ = liftEither . first BE . tCtx
  where
    tCtx tϵ | Just (n,s) <- tun tϵ = β cϵ n s | otherwise = Right tϵ

{-# SCC (@*) #-}
(@*) :: Subst a -> TS a -> TS a
s @* (TS l r) = TS (s@@l) (s@@r)

{-# SCC peek #-}
peek :: Subst a -> TSeq a -> TSeq a
peek _ []          = []
peek s (SV _ n:ts) = let v = s@~>n in if null v then peek s ts else v++ts
peek s (t:ts)      = s@>t:ts

peekS :: Subst a -> TS a -> TS a
peekS s (TS l r) = TS (peek s l) (peek s r)

{-# SCC (@@) #-}
(@@) :: Subst a -> TSeq a -> TSeq a
(@@) _ []          = []
(@@) s (SV _ n:ts) = s@~>n ++ s@@ts
(@@) s (t:ts)      = s@>t : s@@ts

(@~>) :: Subst a -> Nm a -> TSeq a
(@~>) s v@(Nm _ (U i) x) =
    case IM.lookup i (svs s) of
        Just ts -> mapSV (IM.delete i) s @@ ts
        Nothing -> [SV x v]

{-# SCC (@>) #-}
(@>) :: Subst a -> T a -> T a
(@>) _ t@TP{}          = t
(@>) _ t@TT{}          = t
(@>) _ t@TC{}          = t
(@>) s (TA x t0 t1)    = TA x (s@>t0) (s@>t1)
(@>) s (QT x sig)      = QT x (s@*sig)
(@>) s (UU x ts)       = UU x (map (s@>) ts)
(@>) s t@(TV _ (Nm _ (U u) _)) =
    case IM.lookup u (tvs s) of
        Nothing -> t
        Just t' -> s\-u@>t'
(@>) s (Ρ l n@(Nm _ (U u) _) a) =
    case IM.lookup u (tvs s) of
        Nothing -> Ρ l n (fmap (s@@) a)
        Just t' -> s\-u@>t'
(@>) s (Σ x ts) = Σ x (fmap (s@@) ts)
(@>) _ SV{} = error"Internal error: (@>) applied to stack variable "

so :: T a -> IS.IntSet
so (SV _ n)        = NmSet.singleton n
so (TA _ t₀ t₁)    = so t₀<>so t₁
so TP{}            = IS.empty
so (UU _ ts )      = so@<>ts
so (QT _ (TS l r)) = so@<>l <> so@<>r
so TT{}            = IS.empty
so TC{}            = IS.empty
so (Σ _ a)         = foldMap (so@<>) a
so (Ρ _ _ σ)       = foldMap (so@<>) σ
so TV{}            = IS.empty

occ :: T a -> IS.IntSet
occ (TV _ n)        = NmSet.singleton n
occ (TA _ t0 t1)    = occ t0<>occ t1
occ TP{}            = IS.empty
occ (UU _ ts)       = occ@<>ts
occ (QT _ (TS l r)) = occ@<>l <> occ@<>r
occ TT{}            = IS.empty
occ TC{}            = IS.empty
occ SV{}            = IS.empty
occ (Σ _ a)         = foldMap (occ@<>) a
occ (Ρ _ n a)       = NmSet.insert n$foldMap (occ@<>) a

occρ :: Nm a -> Nm.NmMap (TSeq a) -> Bool
occρ n σ = n `NmSet.member` foldMap (occ@<>) σ

roll = foldr (\t₀ -> TA (tL t₀) t₀)

nv s n σ t e eo | n `NmSet.member` occ t = throwError eo
                 | Nm.null σ = pure (t, iTV n t s)
                 | otherwise = throwError e

uu :: Nt a -> Subst a -> T a -> T a -> UM a (T a, Subst a)
uu _ s t@(TV _ n₀) (TV _ n₁) | n₀==n₁ = pure (t,s)
uu _ s t@(Ρ _ ρ₀ _) (Ρ _ ρ₁ _) | ρ₀==ρ₁ = pure (t,s)
uu _ s t0@(TV _ n) t1 = (t1,) <$> ci n t1 t0 s
uu _ s t0 t1@(TV _ n) = (t0,) <$> ci n t0 t1 s
uu c s t0 t1 | Just (th@(TC _ n0), a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = do
    (a',s') <- zS (uu c) s a0 a1
    pure (roll th a',s')
uu c s (TC _ n) t1 = do {t0 <- lC (tβ c) n; uu c s t0 t1}
uu c s t0 (TC _ n) = do {t1 <- lC (tβ c) n; uu c s t0 t1}
uu _ s t0@(TT _ tt₀) t1@(TT _ tt₁) | tt₀==tt₁ = pure (t0,s)
                                   | otherwise = throwError$UF t0 t1
uu c s t0@(Σ l as₀) t1@(Σ _ as₁) | eqKeys as₀ as₁ = first (Σ l) <$> uσ uus c s l as₀ as₁ -- shouldn't have stack vars hm
                                 | otherwise = throwError$UF t0 t1
uu c s t0@(Σ _ as) t1@(Ρ l n σ) | n `occρ` as = throwError$O t0 t1
                                | σ `Nm.isSubmapOf` as = do {(σ',s') <- uσ uus c s l as σ; second ($s') <$> nρ n σ'}
                                | otherwise = throwError$UF t0 t1
uu c s t0@(Ρ l n σ) t1@(Σ _ as) | n `occρ` as = throwError$O t0 t1
                                | σ `Nm.isSubmapOf` as = do {(σ',s') <- uσ uus c s l as σ; second ($s') <$> nρ n σ'}
                                | otherwise = throwError$UF t0 t1
uu c s t0@(Ρ l n0 σ0) t1@(Ρ _ n1 σ1) | n0 `occρ` σ1 = throwError$O t0 t1
                                     | n1 `occρ` σ0 = throwError$O t1 t0
                                     | eqKeys σ0 σ1 = do {(σ,s') <- uσ uus c s l σ0 σ1; second ($s') <$> nρ n0 σ}
                                     -- TODO: Ρ, Σ case above only requires one be a submap... perhaps this is too strict?
uu _ s t0@(TP _ p0) t1@(TP _ p1) | p0==p1 = pure (t0,s)
                                 | otherwise = throwError$UF t0 t1
uu c s (QT x (TS l0 r0)) (QT _ (TS l1 r1)) = do {(l',s') <- usc c s l0 l1; (r',s'') <- usc c s' r0 r1; pure (QT x (l'--:r'), s'')}
uu c s (UU x ts) t1 = do {t0 <- uU (tβ c) x ts; uu c s t0 t1}
uu c s t0 (UU x ts) = do {t1 <- uU (tβ c) x ts; uu c s t0 t1}
uu _ s te@(Ρ _ n σ) t = nv s n σ t (UF te t) (O te t)
uu _ s t te@(Ρ _ n σ) = nv s n σ t (UF t te) (O t te)
uu _ _ t0@TP{} t1 = throwError$UF t0 t1
uu _ _ t0 t1@TP{} = throwError$UF t0 t1
uu _ _ t0@QT{} t1 = throwError$UF t0 t1
uu _ _ t0 t1@QT{} = throwError$UF t0 t1
uu _ _ SV{} _ = ie; uu _ _ _ SV{} = ie

uus=sv uu;usc=ctx'ize uus

{-# SCC su #-}
-- "subsumes"
su :: Nt a -> Subst a -> T a -> T a -> UM a (T a, Subst a)
su _ s t@(TV _ n0) (TV _ n1) | n0==n1 = pure (t,s)
su _ s t@(Ρ _ n0 _) (Ρ _ n1 _) | n0==n1 = pure (t,s)
su _ s t0@(TV _ n) t1 = (t1,) <$> ci n t1 t0 s
su _ s t0 t1@(TV _ n) = (t0,) <$> ci n t0 t1 s
su c s (QT x (TS l0 r0)) (QT _ (TS l1 r1)) = do
    -- contravariant
    (l',s₀) <- susc c s l1 l0
    (r',s₁) <- susc c s₀ r0 r1
    pure (QT x (l' --: r'), s₁)
    -- [tag:constant]
su c s t0 t1 | Just (th@(TC _ n0), a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = do
    (a',s') <- zS (su c) s a0 a1
    pure (roll th a',s')
su c s (TC _ n) t1 = do {t0 <- lC (tβ c) n; su c s t0 t1}
su c s t0 (TC _ n) = do {t1 <- lC (tβ c) n; su c s t0 t1}
su c s t0 t1 | Just{} <- unA t0 = do {t0' <- lΒ (tβ c) t0; su c s t0' t1}
su c s t0 t1 | Just{} <- unA t1 = do {t1' <- lΒ (tβ c) t1; su c s t0 t1'}
su c s t0@(Ρ _ n σ0) t1@(Σ x σ1) | σ0 `Nm.isSubmapOf` σ1 = do
    -- TODO propagate back?
    (ς,s') <- sσ c s x σ0 σ1
    (n',g) <- ρc n (σ0<>σ1<>ς) t0
    pure (n',g s')
                                 | otherwise = cf t0 t1
su c s (Σ x σ0) t@(Ρ _ n σ1) = do
    (ς,s') <- sσ c s x σ0 σ1
    (n',g) <- ρc n (σ0<>σ1<>ς) t
    pure (n',g s')
su _ s t0@(TT _ tt) t1@(Ρ _ n σ) =
    case Nm.lookup tt σ of
        -- don't propagate back?
        Nothing -> do {(n',g) <- nρ n (Nm.insert tt [] σ); pure (n',g s)}
        Just [] -> pure (t1, s)
        Just _  -> sf t0 t1
su c s (Ρ x n0 σ0) t1@(Ρ _ _ σ1) = do
    (ς,s') <- sσ c s x σ0 σ1
    (n',g) <- ρc n0 (σ0<>σ1<>ς) t1
    pure (n',g s')
su _ s t0@(TT _ tt0) t1@(TT _ tt1) | tt0==tt1 = pure (t0, s)
                                   | otherwise = cf t0 t1
su _ s t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure (t0, s)
                                 | otherwise = cf t0 t1
su c s t0@(Σ x a0) t1@(Σ _ a1) | a0 `Nm.isSubmapOf` a1 = do {(ς,s') <- sσ c s x a0 a1; pure (Σ x ς, s')}
                               | otherwise = cf t0 t1
                              -- TODO: should we check TT has arity 0?
su _ _ t0@(TT _ n) t1@(Σ _ σ) | Just [] <- Nm.lookup n σ = pure (t0, mempty)
                              | otherwise = cf t0 t1
su _ _ t0@(Σ _ σ) t1@(TT _ n) | [(n₀,[])] <- Nm.toList undefined σ, n==n₀ = pure (t0, mempty)
                              | otherwise = cf t0 t1
su c s (UU x ts) t1 = do {t0 <- uU (tβ c) x ts; su c s t0 t1}
su c s t0 (UU x ts) = do {t1 <- uU (tβ c) x ts; su c s t0 t1}
su _ s t te@(Ρ _ n σ) = nv s n σ t (CF t te) (O t te)
su _ s te@(Ρ _ n σ) t = nv s n σ t (CF te t) (O te t)
su _ _ t0@QT{} t1 = cf t0 t1; su _ _ t0 t1@QT{} = cf t0 t1
su _ _ t0@TP{} t1 = cf t0 t1; su _ _ t0 t1@TP{} = cf t0 t1
su _ _ t0@TT{} t1 = cf t0 t1; su _ _ t0 t1@TT{} = cf t0 t1
su _ _ SV{} _ = ie; su _ _ _ SV{} = ie

uσ u c s l σ0 σ1 =
    us s (Nm.toList l ς)
  where
    ς=Nm.intersectionWith (,) σ0 σ1

    us sϵ []              = pure (Nm.empty, sϵ)
    us sϵ ((n,(x,y)):xys) = do {(xy,s') <- u c sϵ x y; first (Nm.insert n xy) <$> us s' xys}

sus=sv su;susc=ctx'ize sus; sσ = uσ susc

type UC v a = Nt a -> Subst a -> v -> v -> UM a (v, Subst a)

si :: Nm a -> TSeq a -> UM a (Subst a -> Subst a)
si n₀ [SV _ n₁] | n₀==n₁ = pure id
-- if we have A, B [B c -- A b] (say) then say A=0
si n₀ t@(SV _ n₁:_) | n₀ `NmSet.member` so@<>t = if n₀==n₁ then throwError (Os n₀ t) else pure (iSV n₀ [])
si n t = pure (iSV n t)

sv :: UC (T a) a -> UC (TSeq a) a
sv _ _ s [] [] = pure ([], s)
sv u c s t0@(SV _ sn0:t0d) t1@(SV _ sn1:t1d) =
    let n0=length t0d; n1=length t1d in
    case compare n0 n1 of
        GT -> let (uws, res) = splitFromLeft n1 t0
              in do {ς <- si sn1 uws; first (uws++) <$> ctx'ize (sv u) c (ς s) res t1d}
        _  -> let (uws, res) = splitFromLeft n0 t1
              in do {ς <- si sn0 uws; first (uws++) <$> ctx'ize (sv u) c (ς s) t0d res}
sv u c s t0@(SV _ sn0:t0d) t1 =
    let n0=length t0d; n1=length t1 in
    case compare n0 n1 of
        GT -> throwError$LE t0 t1
        _  -> let (uws, res) = splitFromLeft n0 t1
        -- TODO: why iSV vs. ς?
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn0 uws s) t0d res
sv u c s t0 t1@(SV _ sn1:t1d) =
    let n0=length t0; n1=length t1d in
    case compare n0 n1 of
        LT -> throwError$LE t1 t0
        _  -> let (uws, res) = splitFromLeft n1 t0
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn1 uws s) res t1d
sv u c s (t0:ts0) (t1:ts1) = do
    (t',s') <- u c s t0 t1
    first (t':) <$> ctx'ize (sv u) c s' ts0 ts1
sv _ _ _ t0 [] = throwError$LE t0 []
sv _ _ _ [] t1 = throwError$LE t1 []

ctx'ize us c s = us c s `onM` (rwAr (ars c).peek s)

ρc :: Nm a -> Nm.NmMap (TSeq a) -> T a -> UM a (T a, Subst a -> Subst a)
ρc n σ te | occρ n σ = throwError $ O (TV (Nm.loc n) n) te
          | otherwise = nρ n σ

-- fan out
nρ n@(Nm t _ l) σ = do
    n' <- fr l t
    let t'=Ρ l n' σ
    pure (t', iTV n t')

φ :: Nt a -> Subst a -> T a -> T a -> UM a (T a, Subst a)
φ _ s t@(TT x n0) (TT _ n1) | n0==n1 = pure (t,s)
                            | otherwise = pure (Σ x (Nm.fromList [(n0,[]),(n1,[])]), s)
φ _ s (Σ _ as) (TT x n) = pure (Σ x (Nm.insert n [] as), s)
φ _ s (TT x n) (Σ _ as) = pure (Σ x (Nm.insert n [] as), s)
φ _ s (Σ x σ0) (Σ _ σ1) = pure (Σ x (σ0<>σ1), s)
φ _ s t@(TV _ n0) (TV _ n1) | n0==n1 = pure (t,s)
                            | otherwise = pure (t, iTV n1 t s)
φ _ s t0@(TV _ n) t1 = (t1,) <$> ci n t1 t0 s
φ _ s t0 t1@(TV _ n) = (t0,) <$> ci n t0 t1 s
φ c s t@(Σ _ as) (Ρ x n σ) = do
    (ς, s') <- φσ c s x σ as
    (n',g) <- ρc n (σ<>as<>ς) t
    pure (n', g s')
φ c s (Ρ x n σ) t@(Σ _ as) = do
    (ς, s') <- φσ c s x σ as
    (n',g) <- ρc n (σ<>as<>ς) t
    pure (n', g s')
φ _ s t0@(TT _ tt) t1@(Ρ _ n σ) =
    case Nm.lookup tt σ of
        Just [] -> pure (t1,s)
        Just _  -> φf t0 t1
        _ -> do
            -- FIXME: propagates back too much?
            (n',g) <- nρ n (Nm.insert tt [] σ)
            pure (n',g s)
φ _ s t0@(Ρ _ n σ) t1@(TT _ tt) =
    case Nm.lookup tt σ of
        Just [] -> pure (t0,s)
        Just _  -> φf t0 t1
        _ -> do
            -- FIXME: propagates back too much?
            (n',g) <- nρ n (Nm.insert tt [] σ)
            pure (n',g s)
φ c s t0 t1 | Just (th@(TC _ n0), a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = do
    (a',s') <- zS (φ c) s a0 a1
    pure (roll th a',s')
φ c s (TC _ n) t1 = do {t0 <- lC (tβ c) n; φ c s t0 t1}
φ c s t0 (TC _ n) = do {t1 <- lC (tβ c) n; φ c s t0 t1}
φ c s t0 t1 | Just{} <- unA t0 = do {t0' <- lΒ (tβ c) t0; φ c s t0' t1}
φ c s t0 t1 | Just{} <- unA t1 = do {t1' <- lΒ (tβ c) t1; φ c s t0 t1'}
φ c s (Ρ x n σ0) t@(Ρ _ _ σ1) = do
    (ς, s') <- φσ c s x σ0 σ1
    -- FIXME: propagates back too much?
    (n',g) <- ρc n (σ0<>σ1<>ς) t
    pure (n', g s')
φ c s (UU x ts) t1 = do {t0 <- uU (tβ c) x ts; φ c s t0 t1}
φ c s t0 (UU x ts) = do {t1 <- uU (tβ c) x ts; φ c s t0 t1}
φ _ s t te@(Ρ _ n σ) = nv s n σ t (ΦF t te) (O t te)
φ _ s te@(Ρ _ n σ) t = nv s n σ t (ΦF te t) (O t te)
φ _ s t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure (t0, s)
                                | otherwise = φf t0 t1
φ c s t0@QT{} t1@QT{} = uu c s t0 t1
φ _ _ t0@TP{} t1 = φf t0 t1
φ _ _ t0 t1@TP{} = φf t0 t1
φ _ _ t0@TT{} t1@QT{} = φf t0 t1
φ _ _ t0@QT{} t1@TT{} = φf t0 t1
φ _ _ SV{} _ = ie; φ _ _ _ SV{} = ie

φs=sv φ;φsc=ctx'ize φs; φσ = uσ φsc

-- FIXME: eat into stack var when present
rwAr :: Ar -> TSeq a -> UM a (TSeq a)
rwAr ar = under (fmap reverse . g . reverse)
    where g (tt@(TT x n):ts) = do {k <- lT ar n; if length ts>=k then let (a,r)=splitAt k ts in (Σ x (Nm.singleton n (reverse a)):)<$>g r else (tt:) <$> g ts}
          g (t:ts)           = (t:)<$>g ts
          g []               = pure []

          under f (t@SV{}:ts) = (t:)<$>f ts
          under f ts          = f ts

mc u c s = ms u c s `onM` (rwAr (ars c).peek s)

-- TODO: check agreement w.r.t. previous agreements... e.g.
-- a b c
-- d e d
ms :: (Nt a -> T a -> T a -> UM a (Subst a))
   -> Nt a -> Subst a
   -> TSeq a -- ^ inferred
   -> TSeq a -- ^ signature
   -> UM a (Subst a)
ms u c s t0e@(SV _ nm₀:t0) t1e@(SV _ nm₁:t1)
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in mc u c (iSV nm₀ []$iSV nm₁ uws s) t0 res
    -- FIXME: eat based on constructor arity?
    | otherwise = throwError$LE t0e t1e
  where n0=length t0;n1=length t1
ms u c s t0e@(SV _ n:t0) t1
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in mc u c (iSV n uws s) t0 res
    | otherwise = throwError$LE t0e t1
  where n0=length t0;n1=length t1
ms u c s t0 t1e@(SV _ n:t1)
    | n0>=n1 = let (uws, res) = splitFromLeft n1 t0
               in mc u c (iSV n uws s) res t1
    | otherwise = throwError$LE t1e t0
  where n0=length t0; n1=length t1
ms u c s (t0:t0s) (t1:t1s) = do {s' <- u c t0 t1; mc u c (s<>s') t0s t1s}
ms _ _ s [] [] = pure s
ms _ _ _ t0 [] = throwError$LE t0 []
ms _ _ _ [] t1 = throwError$LE t1 []

mσ u c σ0 σ1 =
    execStateT (traverse (uncurry g) (Nm.intersectionWith (,) σ0 σ1)) mempty
  where
    g t0 t1 = do {s <- get; s' <- lift (mc u c s t0 t1); put s'}

{-# SCC μ #-}
μ :: Nt a
  -> T a -- ^ inferred
  -> T a -- ^ sig
  -> UM a (Subst a)
μ _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
μ _ t0@(TV _ n) t1 = c1 n t1 t0
μ _ t0@(Ρ _ n σ) t1 | Nm.null σ = c1 n t1 t0
μ _ t0 t1@TV{} = throwError$MF t0 t1
μ c (Σ _ σ0) (Σ _ σ1) = mσ μ c σ0 σ1
μ c (Ρ _ _ σ0) (Σ _ σ1) = mσ μ c σ0 σ1 -- find universality but do not substitute so we can check case coverage later
-- TODO: this proceeds the same as [ref:expand] in expanding constants...
μ c t0 t1 | Just (TC _ n0, a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = ms μ c mempty a0 a1
μ c (TC _ n) t1 = do {t0 <- lC (tβ c) n; μ c t0 t1}
μ c t0 (TC _ n) = do {t1 <- lC (tβ c) n; μ c t0 t1}
μ c t0 t1 | Just{} <- unA t0 = do {t0' <- lΒ (tβ c) t0; μ c t0' t1}
μ c t0 t1 | Just{} <- unA t1 = do {t1' <- lΒ (tβ c) t1; μ c t0 t1'}
μ c (UU x ts) t1 = do {t0 <- uU (tβ c) x ts; μ c t0 t1}
μ c t0 (UU x ts) = do {t1 <- uU (tβ c) x ts; μ c t0 t1}
μ _ TP{} TP{} = pure mempty
μ c (QT _ ts0) (QT _ ts1) = μs c mempty ts0 ts1
μ _ t0@TP{} t1@Σ{} = throwError$MF t0 t1
μ _ t0@Σ{} t1@TP{} = throwError$MF t0 t1
μ _ (TT _ n0) (TT _ n1) | n0==n1 = pure mempty
μ _ t0 t1@TP{} = throwError$MF t0 t1
μ _ t0 t1@QT{} = throwError$MF t0 t1
μ _ SV{} _ = ie; μ _ _ SV{} = ie

-- ≺
lt :: Nt a -> T a -> T a -> UM a (Subst a)
lt c t0@(Σ _ σ0) t1@(Σ _ σ1) | σ0 `Nm.isSubmapOf` σ1 = mσ lt c σ0 σ1
                             | otherwise = sf t0 t1
lt _ t0@(TT _ tt0) t1@(TT _ tt1) | tt0==tt1 = pure mempty
                                 | otherwise = sf t0 t1
lt _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
lt _ t0 t1@(Ρ _ n σ) | Nm.null σ = c1 n t0 t1
lt _ t0@(Ρ _ n σ) t1 | Nm.null σ = c1 n t1 t0
lt _ t0 t1@TV{} = sf t0 t1
lt _ t0@TV{} t1 = sf t0 t1
lt c (QT _ ts0) (QT _ ts1) = lts c mempty ts0 ts1
-- [tag:expand]
lt c t0 t1 | Just (TC _ n0, a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = ms lt c mempty a0 a1
lt c (TC _ n) t1 = do {t0 <- lC (tβ c) n; lt c t0 t1}
lt c t0 (TC _ n) = do {t1 <- lC (tβ c) n; lt c t0 t1}
lt c t0 t1 | Just{} <- unA t0 = do {t0' <- lΒ (tβ c) t0; lt c t0' t1}
lt c t0 t1 | Just{} <- unA t1 = do {t1' <- lΒ (tβ c) t1; lt c t0 t1'}
lt c t0@(Ρ _ n σ0) t1@(Σ _ σ1)
    | occρ n σ1 = throwError$O t0 t1
    | σ0 `Nm.isSubmapOf` σ1 = iTV n t1 <$> mσ lt c σ0 σ1
    | otherwise = sf t0 t1
    -- TODO: Σ, TT
lt _ t0@(TT _ n) t1@(Σ _ a) | Just [] <- Nm.lookup n a = pure mempty
                            | otherwise = sf t0 t1
lt c t0@(Σ _ σ0) t1@(Ρ _ n σ1) | occρ n σ0 = throwError$O t1 t0
                               | otherwise = do {(_,g) <- nρ n (σ0<>σ1); g<$>mσ lt c σ0 σ1} -- [tag:fresh]
lt _ t@QT{} (Ρ _ n σ) | Nm.null σ = pure (sTV n t)
-- lt _ (Ρ _ n σ) t@QT{} | Nm.null σ = pure (sTV n t) TODO?
lt c t0@(Ρ _ n0 σ0) t1@(Ρ _ n1 σ1) | occρ n0 σ1 = throwError$O t0 t1
                                   | occρ n1 σ0 = throwError$O t1 t0
                                   -- FIXME: we do exactly the opposite in [ref:fresh]
                                   | σ0 `Nm.isSubmapOf` σ1 = mσ lt c σ0 σ1
                                   | otherwise = sf t0 t1
lt _ t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure mempty
                               | otherwise = sf t0 t1
lt c (UU x ts) t1 = do {t0 <- uU (tβ c) x ts; lt c t0 t1}
lt c t0 (UU x ts) = do {t1 <- uU (tβ c) x ts; lt c t0 t1}
lt _ t0@TP{} t1@QT{} = sf t0 t1; lt _ t0@QT{} t1@TP{} = sf t0 t1
lt _ t0@TP{} t1@TT{} = sf t0 t1; lt _ t0@TT{} t1@TP{} = sf t0 t1
lt _ t0@TT{} t1@QT{} = sf t0 t1; lt _ t0@QT{} t1@TT{} = sf t0 t1
lt _ t0@TP{} t1@Σ{} = sf t0 t1; lt _ t0@Σ{} t1@TP{} = sf t0 t1
lt _ t0@QT{} t1@Σ{} = sf t0 t1; lt _ t0@Σ{} t1@QT{} = sf t0 t1
lt _ SV{} _ = ie; lt _ _ SV{} = ie

{-# SCC uU #-}
uU :: Cs a -> a -> [T a] -> UM a (T a)
uU c x ts = Σ x <$> foldMapM f ts where
    f (TT _ n)   = pure (Nm.singleton n [])
    f (Σ _ σ)    = pure σ
    f (TC _ n)   = f =<< lC c n
    f t          | Just{} <- unA t = f =<< lΒ c t
    f (UU _ ts_) = foldMapM f ts_
    -- FIXME: unions on variables? (could end up being instantiated wrong...)
    f SV{}       = ie
    f Ρ{}        = ie
    f TP{}       = throwError$Bare (UU x ts)
    f QT{}       = throwError$Bare (UU x ts)

μs, lts :: Nt a -> Subst a
        -> TS a -- ^ inferred
        -> TS a -- ^ signature
        -> UM a (Subst a)
μs c s (TS l0 r0) (TS l1 r1) = do {s' <- mc μ c s l0 l1; mc μ c s' r0 r1}
lts c s (TS l0 r0) (TS l1 r1) = do {s' <- mc (\cϵ t0 t1 -> lt cϵ t1 t0) c s l0 l1; mc lt c s' r0 r1} -- TODO: why flip lt instead of l1 l0...?

{-# SCC mtsc #-}
mtsc :: Nt a -> Subst a -> TS a -> TS a -> UM a (Subst a)
mtsc c s ts0 ts1 = do {s' <- μs c s ts0 ts1; lts c s' ts0 ts1}

liftClone :: TS a -> UM a (TS a)
liftClone ts = StateT $ \u -> let (w, ts') = cloneSig u ts in Right (ts',w)

lC :: Cs a -> Nm a -> UM a (T a)
lC c n@(Nm _ (U i) l) = do
    case IM.lookup i c of
        Just ([],t) -> pure (t$>l)
        Nothing     -> throwError$IS n

lT :: Ar -> Nm a -> UM a Int
lT ar n@(Nm _ (U u) _) = do
    case IM.lookup u ar of
        Just i  -> pure i
        Nothing -> throwError$AM n

lA :: IM.IntMap (TS a) -> Nm a -> UM a (TS a)
lA c n@(Nm _ (U i) l) = do
    case IM.lookup i c of
        Just ts -> (l<$) <$> liftClone ts
        Nothing -> throwError$IS n

tM :: Ext a -> M a a -> UM a (M a (TS a), Ext a)
tM b (M is ds) = first (M is) <$> tD b ds

tD :: Ext a -> [D a a] -> UM a ([D a (TS a)], Ext a)
tD b ds = do {(_,c) <- liftTM (traverse_ tD0 ds); (,c) <$> traverse (tD1 (c<>b)) ds}

tAS :: Int -> Ext a -> [A (TS a)] -> ASeq a -> Either (TE a) ((TS a, ASeq (TS a)), Int)
tAS u b s a = flip runStateT u $ do
    (t0,s0) <- sseq n (aLs a) mempty (reverse s)
    (t1,s1) <- tseq b s0 a
    (t2,s2) <- cat n s1 t0 (aLs t1)
    pure (s2@*t2, faseq (s2@*) t1)
  where n=π b

{-# SCC tD0 #-}
tD0 :: D a a -> TM a ()
tD0 (F _ n ts _)  = iFn n ts
tD0 (TD _ n vs t) = iTD n vs t *> cA t

{-# SCC tD1 #-}
tD1 :: Ext a -> D a a -> UM a (D a (TS a))
tD1 _ (TD x n vs t) = pure (TD x n vs t)
tD1 c (F _ n ts as) = do
    (as', s) <- tseq c mempty as
    s' <- mtsc (π c) s (aLs as') ts
    pure (F ts (n$>ts) ts (faseq (s'@*) as'))

-- TODO check that user-supplied signatures have at most one stack variable, and that it occurs at the leftmost
iFn (Nm _ (U i) _) ts = modify (\(TSt m (Ext f c a)) -> TSt m (Ext (IM.insert i ts f) c a))
iTD (Nm _ (U i) _) vs t = modify (\(TSt m (Ext f c a)) -> TSt m (Ext f (IM.insert i (vs,t) c) a))

cA :: T a -> TM b ()
cA (UU _ ts) = traverse_ cA ts
cA (Σ _ t) = modify (\(TSt m (Ext f c a)) -> TSt m (Ext f c (fmap length (Nm.xx t)</>a)))
    where (</>) x y | rs <- IM.intersectionWith (,) x y, all (uncurry (==)) rs = x<>y
                    | otherwise = error"sum declaration includes tag with conflicting arity"
cA _=pure ()

sseq :: Nt a -> a -> Subst a -> [A (TS a)] -> UM a (TS a, Subst a)
sseq b l s as = do {a <- fsv l "A"; γ s ([a] --: [a]) as}
  where
    γ sϵ tl []     = pure (tl, sϵ)
    γ sϵ tl (a:aa) = do {(t',s') <- cat b sϵ tl (aL a); γ s' t' aa}

tseq :: Ext a -> Subst a -> ASeq a -> UM a (ASeq (TS a), Subst a)
tseq b s (SL l as) = do {a <- fsv l "A"; tγ s (SL ([a] --: [a]) []) as}
  where
    tγ sϵ c []              = pure (c, sϵ)
    tγ sϵ (SL t al) (a:aa) = do
        (a',s0) <- tae b sϵ a
        (t',s1) <- cat (π b) s0 t (aL a')
        tγ s1 (SL t' (al++[a'])) aa

(/|) :: [a] -> Int -> ([a], [a])
xs /| n = splitFromLeft n xs

splitFromLeft :: Int -> [a] -> ([a], [a])
splitFromLeft n xs | nl <- length xs = splitAt (nl-n) xs

{-# SCC cat #-}
cat :: Nt a -> Subst a -> TS a -> TS a -> UM a (TS a, Subst a)
cat c s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- susc c s r0 l1
    pure (l0 --: r1, s')

fr :: a -> T.Text -> UM a (Nm a)
fr l t = state (\m -> let n=m+1 in (Nm t (U n) l, n))

ftv, fsv, erv :: a -> T.Text -> UM a (T a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)
erv l n = Ρ l <$> fr l n <*> pure Nm.empty

exps :: a -> TS a -> UM a (TS a)
exps _ t@(TS (SV{}:_) _) = pure t; exps _ t@(TS _ (SV{}:_)) = pure t
exps x (TS l r) = do {ᴀ <- fsv x "A"; pure (ᴀ:l --: ᴀ:r)}

tae :: Ext a -> Subst a -> A a -> UM a (A (TS a), Subst a)
tae _ s (B l Dip)  = do {a <- fsv l "A"; b <- ftv l "b"; c <- fsv l "C"; pure (B ([a, b, QT l ([a] --: [c])] --: [c,b]) Dip, s)}
tae _ s (B l Ap) = do {a <- fsv l "A"; b <- fsv l "B"; pure (B ([a, QT l ([a] --: [b])] --: [b]) Ap, s)}
tae b s a = do
    (a',s') <- ta b s a
    let t=aL a'
    t' <- exps (aL a) t
    pure (a' {aL = t'}, s')

ib l = B ([TP l Int, TP l Int] --: [TP l Int])
rel l = B ([TP l Int, TP l Int] --: [ʙ l])

ta :: Ext a -> Subst a -> A a -> UM a (A (TS a), Subst a)
ta _ s (L l lit@I{})   = pure (L ([] --: [TP l Int]) lit, s)
ta _ s (L l lit@Str{}) = pure (L ([] --: [TP l String]) lit, s)
ta _ s (L l (S p)) = do
    ns <- traverse (\_ -> ftv l "a") (indices p)
    pure (L (ns --: reverse (p `gp` reverse ns)) (S p), s)
ta b s (V _ n)         = do {ts <- lA (fns b) n; pure (V ts (n$>ts), s)}
ta _ s (B l Un)        = do {n <- ftv l "a"; pure (B ([n] --: []) Un, s)}
ta _ s (B l Dup)       = do {n <- ftv l "a"; pure (B ([n] --: [n,n]) Dup, s)}
ta _ s (B l Plus)      = pure (ib l Plus, s)
ta _ s (B l Minus)     = pure (ib l Minus, s)
ta _ s (B l Mul)       = pure (ib l Mul, s)
ta _ s (B l Div)       = pure (ib l Div, s)
ta _ s (B l Rem)       = pure (ib l Rem, s)
ta _ s (B l Eq)        = pure (rel l Eq, s)
ta _ s (B l Gt)        = pure (rel l Gt, s)
ta _ s (B l Lt)        = pure (rel l Lt, s)
ta b s (Q l as)        = do {(as', s') <- tseq b s as; pure (Q ([] --: [QT l (aLs as')]) as', s')}
ta b s (Inv _ a)       = do {(a', s') <- ta b s a; let TS l r = aL a' in pure (Inv (r--:l) a', s')}
ta b s (C l tt)        = do
    p <- lT (arit b) tt
    -- TODO: pad beginning not-inverse constructors with a₀ etc. not ρ₀?
    ρ <- pad l p
    let ts=TS ρ (ρ++[TT l tt]) in pure (C ts (tt$>ts), s)
ta b s (Pat l as)      = do
    (as', s0) <- tS b s (aas as)
    let sigs = map (peekS s0.aLs) as'
    (t, s1) <- dU (π b) s0 l sigs
    pure (Pat t (SL t as'), s1)

pad :: a -> Int -> UM a (TSeq a)
pad l n = traverse (\i -> erv l ("ρ"<>pᵤ i)) [1..n]

tally :: [([(Nm a, TSeq a)], TS a)] -> Nm.NmMap [TS a]
tally = foldl' (\z (ns,TS l r) -> thread [Nm.insertWith (++) n [TS (l++υ) r] | (n,υ) <- ns] z) Nm.empty

ψ :: Nt a -> [TS a] -> UM a (Nm.NmMap [TS a])
ψ c tss = do
    n <- minimum <$> traverse g sl
    when (n==0) $ throwError (PM (head$map tlefts tss))
    forks <- traverse (p n) sl
    h <- traverse (l n) sl
    let tss' = zipWith TS (map reverse h) (map trights tss)
    -- TODO: fuse with p below
    pure (tally (zip forks tss'))
    where sl=map (reverse.tlefts) tss

    -- counts, punches hole, picks out "pivot name" all separately...
    -- probably should map this one or two traversals...
    --
    -- also maybe "count by arity backwards" mishandles just⁻¹ drop `true⁻¹
          l :: Int -> [T a] -> UM a [T a]
          l 1 (_:ts)           = pure ts
          l n (t@Σ{}:ts)       = (t:) <$> l (n-1) ts
          l n (t@(TT _ tt):ts) = do {k <- lψ tt; (t:).(take k ts++) <$> l (n-1) ts}
          -- TODO: UU?
          l n (t:ts)           = (t:) <$> l n ts

          p :: Int -> [T a] -> UM a [(Nm a, TSeq a)]
          p n ts = cs =<< (ts!*n) where cs = \case
                                            TT _ nm -> pure [(nm,[])] -- FIXME: we don't pad tags but we DO pad constructors... this can probably be simplified!
                                            Σ x σ -> traverse (\nm -> do {k <- lψ nm; υ <- pad (loc nm) k; pure (nm,υ)}) (Nm.keys σ x)
                                            t | Just{} <- unA t -> error (show t)
                                            _ -> throwError (PM ts)

          (t:_) !* 1          = pure t
          (Σ{}:ts) !* n       = ts!*(n-1)
          (TC{}:ts) !* n      = ts!*(n-1)
          (TA{}:ts) !* n      = ts!*(n-1)
          ((TT _ tt):ts) !* n = do {k <- lψ tt; drop k ts !* (n-1)}
          (TP{}:ts) !* n      = ts!*n
          (QT{}:ts) !* n      = ts!*n
          (Ρ{}:ts) !* n       = ts!*n
          (TV{}:ts) !* n      = ts!*n

          g ((TT _ tt):ts) = do {n <- lψ tt; (1+) <$> g (drop n ts)}
          g (Σ{}:ts)       = (1+) <$> g ts
          g (TC{}:ts)      = (1+) <$> g ts -- TODO: is this right?
          g (TA{}:ts)      = (1+) <$> g ts
          g []             = pure 0
          g [SV{}]         = pure 0
          g (Ρ{}:ts)       = g ts
          g (TV{}:ts)      = g ts
          g (TP{}:ts)      = g ts
          g (QT{}:ts)      = g ts

          lψ=lT (ars c)

{-# SCC dU #-}
dU :: Nt a -> Subst a -> a -> [TS a] -> UM a (TS a, Subst a)
dU c s x tss = do
    tψ <- ψ c =<< traverse (βt (tβ c)) tss
    rϵ <- traverse (traverse (rwAr ar.trights)) tψ
    let rm=maximum (l<$>concat rϵ)
    ρ <- traverse (traverse (pad x.(rm-).l)) rϵ
    let ψ' = Nm.intersectionWith (zipWith (\p (TS l_ r_) -> TS (tuck p l_) (tuck p r_))) ρ tψ
        rs'= concatMap (map trights) ψ'
    (al,s') <- srs s (Nm.toList x ψ')
    (σ,ul) <- an (map (second tlefts) al)
    (l',s'') <- urs s' ul; (r',s''') <- frs s'' rs'
    pure (l'++[σ] --: r', s''')
  where ar=ars c; lR=lT ar

        l (SV{}:t) = length t; l t=length t

        tuck ts0 (t@SV{}:ts1) = t:ts0++ts1; tuck ts0 ts1=ts0++ts1

        srs sϵ []            = pure ([], sϵ)
        srs sϵ ((n, [ts]):a) = first ((n,ts):) <$> srs sϵ a
        srs _  ((_, []):_)   = ie
        -- TODO: step without tuck/etc.
        srs sϵ ((n, ts):a)   = do {(tϵ,s') <- dU c sϵ (loc n) ts; first ((n,tϵ):) <$> srs s' a}

        frs sϵ [t]    = pure (t, sϵ)
        frs sϵ (t:ts) = do {(tr,s0) <- frs sϵ ts; φsc c s0 tr t}

        -- FIXME: this is not catching everything w/ `just⁻¹ drop True⁻¹ True (for instance)
        urs sϵ [t]    = pure (t, sϵ)
        urs sϵ (t:ts) = do {(tr,s0) <- urs sϵ ts; usc c s0 tr t}

        an as = do
            (tas, tls) <- unzip<$>traverse (\(nm,ts) -> do{n<-lR nm; when (n>length ts) ie $> (ts /| n)}) as
            pure (Σ x (Nm.fromDistinctAscList (zip nms tls)), tas)
          where nms=map fst as

βt :: Cs a -> TS a -> UM a (TS a)
βt c (TS l r) = TS <$> βs c l <*> βs c r

βs :: Cs a -> TSeq a -> UM a (TSeq a)
βs c = traverse q where
    q (TC _ n) = q =<< lC c n
    q t | Just{} <- unA t = lΒ c t
    q t = pure t

tS :: Ext a -> Subst a -> [ASeq a] -> UM a ([ASeq (TS a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

zS op s (t0:t0s) (t1:t1s) = do {(t',s') <- op s t0 t1; first (t':) <$> zS op s' t0s t1s}
zS _ s [] []              = pure ([], s)

eqKeys :: Nm.NmMap a -> Nm.NmMap b -> Bool
eqKeys (Nm.NmMap x0 _) (Nm.NmMap x1 _) = IM.keys x0==IM.keys x1

onM :: Monad m => (b -> b -> m c) -> (a -> m b) -> a -> a -> m c
onM g f x y = do {x' <- f x; y' <- f y; g x' y'}

foldMapM f = foldM (\x y -> (x `mappend`) <$> f y) mempty

ie=error"internal error."
