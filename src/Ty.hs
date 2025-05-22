{-# LANGUAGE TupleSections #-}

module Ty ( TE, Ar, Ext (..), tM, tAS ) where

import           A
import           B
import           C
import           Control.Exception                (Exception)
import           Control.Monad                    (when, zipWithM, (<=<))
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.State.Strict (StateT (StateT), execStateT, get, gets, modify, put, runStateT, state)
import           Data.Bifunctor                   (first, second)
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.IntSet                      as IS
import           Data.List                        (unsnoc)
import qualified Data.Text                        as T
import           Data.Typeable                    (Typeable)
import           Nm
import qualified Nm.Map                           as Nm
import qualified Nm.Set                           as NmSet
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), hardline, hsep, indent, vsep, (<+>))
import           Ty.Clone

infixl 7 \-
infixr 6 @>
infixl 6 @@
infixr 6 @*
infixr 7 @<>

type Ar = IM.IntMap Int
data Nt a = Nt { tβ :: Cs a, ars :: Ar }
π (Ext _ c r) = Nt c r

data Ext a = Ext { fns :: IM.IntMap (TS a), tds :: Cs a, arit :: Ar }

instance Semigroup (Ext a) where (<>) (Ext f0 td0 a0) (Ext f1 td1 a1) = Ext (f0<>f1) (td0<>td1) (a0<>a1)
instance Monoid (Ext a) where mempty = Ext IM.empty IM.empty (IM.fromDistinctAscList [(-2,0),(-1,0)])

data TE a = BE (BE a) | O (T a) (T a)
          | PM (TSeq a)
          | LE (TSeq a) (TSeq a)
          | LF (T a) (T a) | ΦF (T a) (T a) | CF (T a) (T a) | UF (T a) (T a)
          | AM (Nm a) | IS (Nm a)

{-# SCC tLs #-}
tLs :: TSeq a -> a
tLs = tL.head

instance Pretty a => Pretty (TE a) where
    pretty (LE ts0 ts1) = tsc ts0$"length mismatch:" <+> sq ts0 <+> "and" <+> sq ts1
    pretty (AM n)       = pretty (Nm.loc n) <> ":" <+> "unknown arity:" <+> sq n
    pretty (BE e)       = pretty e
    pretty (PM ts)      = pretty (tLs ts) <> ":" <+> "Pattern match arms must begin with an inverse constructor."
    pretty (O t₀ t₁)    = tc t₀$"occurs check failed: " <+> sq t₀ <> "," <+> sq t₁
    pretty (LF t0 t1)   = tc t0$pretty t0 <+> "⊀" <+> pretty t1
    pretty (ΦF t0 t1)   = tc t0$sq t0 <+> "not compatible with" <+> sq t1
    pretty (CF t0 t1)   = tc t0$sq t0 <+> "is not an acceptable argument, expected" <+> sq t1
    pretty (UF t0 t1)   = tc t0$"failed to unify" <+> sq t0 <+> "with" <+> sq t1
    pretty (IS n)       = pretty (Nm.loc n) <> ":" <+> sq n <+> "not in scope."

tc t p = pretty (tL t) <> ":" <+> p
tsc t p = pretty (tLs t) <> ":" <+> p

instance Pretty a => Show (TE a) where show=show.pretty

instance (Typeable a, Pretty a) => Exception (TE a) where

data TSt a = TSt { maxT :: !Int, lo :: !(Ext a) }

type TM x = StateT (TSt x) (Either (TE x))

runTM :: Int -> TM a b -> Either (TE a) (b, Ext a, Int)
runTM u = fmap (\(x, TSt m s) -> (x, s, m)).flip runStateT (TSt u (Ext IM.empty IM.empty (IM.fromDistinctAscList [(-2,0),(-1,0)])))

type Bt a = IM.IntMap (T a)
data Subst a = Subst { tvs :: Bt a, svs :: IM.IntMap (TSeq a) }

instance Pretty (Subst a) where pretty (Subst t s) = "tv" <#> pBound t <##> "sv" <#> pBound s

instance Show (Subst a) where show=show.pretty

instance Semigroup (Subst a) where (<>) (Subst tv0 sv0) (Subst tv1 sv1) = Subst (tv0<>tv1) (sv0<>sv1)
instance Monoid (Subst a) where mempty = Subst IM.empty IM.empty

mapTV f (Subst v s) = Subst (f v) s; mapSV f (Subst v s) = Subst v (f s)
iSV n t = mapSV (IM.insert (unU$un n) t); iTV n t = mapTV (IM.insert (unU$un n) t)
sTV (Nm _ (U u) _) t = Subst (IM.singleton u t) IM.empty

c1 :: Nm a -> T a -> T a -> TM a (Subst a)
c1 (Nm _ (U u) _) t te | u `IS.member` occ t = throwError $ O te t
                       | otherwise = pure (Subst (IM.singleton u t) IM.empty)

ci :: Nm a -> T a -> T a -> Subst a -> TM a (Subst a)
ci n t te s | n `NmSet.member` occ t = throwError $ O te t
            | otherwise = pure (mapTV (IM.insert (unU$un n) t) s)

(\-) s u = mapTV (IM.delete u) s

cf, sf, φf :: T a -> T a -> TM a b
sf t0 t1 = throwError$LF t0 t1
φf t0 t1 = throwError$ΦF t0 t1; cf t0 t1 = throwError$CF t0 t1

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
cA (Σ _ t) = modify (\(TSt m (Ext f c a)) -> TSt m (Ext f c (fmap length (Nm.xx t)</>a)))
  where (</>) x y | rs <- IM.intersectionWith (,) x y, all (uncurry (==)) rs = x<>y
                  | otherwise = error "tag in sum with different arity"
cA _=pure ()

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
(@>) s t@(TV _ (Nm _ (U u) _)) =
    case IM.lookup u (tvs s) of
        Nothing -> pure t
        Just t' -> s\-u@>t'
(@>) s (Ρ l n@(Nm _ (U u) _) a) =
    case IM.lookup u (tvs s) of
        Nothing -> Ρ l n <$> traverse (s@@) a
        Just t' -> s\-u@>t'
(@>) s (Σ x ts) = Σ x <$> traverse (s@@) ts
(@>) _ SV{} = error"Internal error: (@>) applied to stack variable "

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

-- TODO: occurs check at substitution function

nv n σ t | Nm.null σ = iTV n t

-- unifies
uu :: Nt a -> Subst a -> T a -> T a -> TM a (T a, Subst a)
uu _ s t@(TV _ n₀) (TV _ n₁) | n₀==n₁ = pure (t,s)
uu _ s t@(Ρ _ ρ₀ _) (Ρ _ ρ₁ _) | ρ₀==ρ₁ = pure (t,s)
uu _ s t0@(TV _ n) t1 = (t1,) <$> ci n t1 t0 s
uu _ s t0 t1@(TV _ n) = (t0,) <$> ci n t0 t1 s
uu _ s t0@(TT _ tt₀) t1@(TT _ tt₁) = if tt₀==tt₁ then pure (t0,s) else throwError$UF t0 t1
uu c s t0@(Σ l as₀) t1@(Σ _ as₁) | eqKeys as₀ as₁ = first (Σ l) <$> uσ uus c s l as₀ as₁ -- shouldn't have stack vars tho...
                                 | otherwise = throwError$UF t0 t1
uu c s t0@(Σ _ as) t1@(Ρ l n σ) | σ `Nm.isSubmapOf` as = do {(σ',s') <- uσ uus c s l as σ; second ($s') <$> nρ n σ'}
                                | otherwise = throwError$UF t0 t1

uus=sv uu;usc=ctx'ize uus

-- "subsumes"
su :: Nt a -> Subst a -> T a -> T a -> TM a (T a, Subst a)
su _ s t@(TV _ n0) (TV _ n1) | n0==n1 = pure (t,s)
su _ s t@(Ρ _ n0 _) (Ρ _ n1 _) | n0==n1 = pure (t,s)
su _ s t0@(TV _ n) t1 = (t1,) <$> ci n t1 t0 s
su _ s t0 t1@(TV _ n) = (t0,) <$> ci n t0 t1 s
su c s (QT x (TS l0 r0)) (QT _ (TS l1 r1)) = do
    -- contravariant
    (l',s₀) <- susc c s l1 l0
    (r',s₁) <- susc c s₀ r0 r1
    pure (QT x (TS l' r'), s₁)
su c s t0 t1 | Just (th@(TC _ n0), a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = do
    (a',s') <- sus c s a0 a1
    pure (roll th a',s')
su c s t0 t1 | Just{} <- unA t0 = do {t0' <- βc (tβ c) t0; su c s t0' t1}
su c s t0 t1 | Just{} <- unA t1 = do {t1' <- βc (tβ c) t1; su c s t0 t1'}
su c s t0@(Ρ _ n σ0) t1@(Σ x σ1) | σ0 `Nm.isSubmapOf` σ1 = do
    -- FIXME propagate back?
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
        -- FIXME propagate back?
        Nothing -> do {(n',g) <- nρ n (Nm.insert tt [] σ); pure (n',g s)}
        Just [] -> pure (t1, s)
        Just _  -> sf t0 t1
su _ s (Ρ _ n σ) t@TT{} = pure (t, nv n σ t s)
su _ s t@QT{} (Ρ _ n σ) = pure (t, nv n σ t s)
su _ s (Ρ _ n σ) t@QT{} = pure (t, nv n σ t s)
su c s t0@(Ρ x n0 σ0) t1@(Ρ _ _ σ1) = do
    (ς,s') <- sσ c s x σ0 σ1
    (n',g) <- ρc n0 (σ0<>σ1<>ς) t1
    pure (n',g s')
su _ s t0@(TT _ tt0) t1@(TT _ tt1) | tt0==tt1 = pure (t0, s)
                                   | otherwise = cf t0 t1
su _ s t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure (t0, s)
                                 | otherwise = cf t0 t1
su c s t0@(Σ x a0) t1@(Σ _ a1) | a0 `Nm.isSubmapOf` a1 = do {(ς,s') <- sσ c s x a0 a1; pure (Σ x ς, s')}
                               | otherwise = cf t0 t1
su _ _ t0@(TT _ n) t1@(Σ _ σ) | Just [] <- Nm.lookup n σ = pure (t0, mempty)
                              | otherwise = cf t0 t1
su _ _ t0@TT{} t1@TP{} = cf t0 t1
su _ _ t0@TT{} t1@QT{} = cf t0 t1
su _ _ t0@TP{} t1@TT{} = cf t0 t1
su _ _ t0@TP{} t1@QT{} = cf t0 t1
su _ _ t0@QT{} t1@TT{} = cf t0 t1
su _ _ t0@QT{} t1@TP{} = cf t0 t1
su _ _ SV{} _ = ie; su _ _ _ SV{} = ie

uσ u c s l σ0 σ1 =
    us s (Nm.toList l ς)
  where
    ς=Nm.intersectionWith (,) σ0 σ1

    us sϵ []              = pure (Nm.empty, sϵ)
    us sϵ ((n,(x,y)):xys) = do {(xy,s') <- u c sϵ x y; first (Nm.insert n xy) <$> us s' xys}

sus=sv su;susc=ctx'ize sus; sσ = uσ susc

type UC v a = Nt a -> Subst a -> v -> v -> TM a (v, Subst a)

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
        GT | hasC t0d -> do {t0' <- ce (tβ c) t0; sv u c s t0' t1}
        GT -> throwError$LE t0 t1
        _  -> let (uws, res) = splitFromLeft n0 t1
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn0 uws s) t0d res
sv u c s t0 t1@(SV _ sn1:t1d) =
    let n0=length t0; n1=length t1d in
    case compare n0 n1 of
        LT | hasC t0 -> do {t0' <- ce (tβ c) t0; sv u c s t0' t1}
        LT -> throwError$LE t1 t0
        _  -> let (uws, res) = splitFromLeft n1 t0
              in first (uws++) <$> ctx'ize (sv u) c (iSV sn1 uws s) t1d res
sv u c s (t0:ts0) (t1:ts1) = do
    (t',s') <- u c s t0 t1
    first (t':) <$> sv u c s' ts0 ts1
sv _ _ _ t0 [] = throwError$LE t0 []
sv _ _ _ [] t1 = throwError$LE t1 []

ctx'ize us c s = us c s `onM` (rwAr (ars c)<=<peek s)

ρc :: Nm a -> Nm.NmMap (TSeq a) -> T a -> TM a (T a, Subst a -> Subst a)
ρc n σ te | occρ n σ = throwError $ O (TV (Nm.loc n) n) te
          | otherwise = nρ n σ

-- fan out
nρ n@(Nm t _ l) σ = do
    n' <- fr l t
    let t'=Ρ l n' σ
    pure (t', iTV n t')

-- fan out
φ :: Nt a -> Subst a -> T a -> T a -> TM a (T a, Subst a)
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
φ _ s t@TP{} (Ρ _ n σ) = pure (t, nv n σ t s)
φ _ s (Ρ _ n σ) t@TP{} = pure (t, nv n σ t s)
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
    (a',s') <- φs c s a0 a1
    pure (roll th a',s')
φ c s t0 t1 | Just{} <- unA t0 = do {t0' <- βc (tβ c) t0; φ c s t0' t1}
φ c s t0 t1 | Just{} <- unA t1 = do {t1' <- βc (tβ c) t1; φ c s t0 t1'}
φ c s (Ρ x n σ0) t@(Ρ _ _ σ1) = do
    (ς, s') <- φσ c s x σ0 σ1
    -- FIXME: propagates back too much?
    (n',g) <- ρc n (σ0<>σ1<>ς) t
    pure (n', g s')
φ _ s t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure (t0, s)
                                | otherwise = φf t0 t1
φ _ _ t0@TP{} t1@QT{} = φf t0 t1
φ _ _ t0@TP{} t1@TT{} = φf t0 t1
φ _ _ t0@TT{} t1@QT{} = φf t0 t1
φ _ _ t0@TT{} t1@TP{} = φf t0 t1
φ _ _ t0@QT{} t1@TP{} = φf t0 t1
φ _ _ t0@QT{} t1@TT{} = φf t0 t1
φ _ _ SV{} _ = ie; φ _ _ _ SV{} = ie

φs=sv φ;φsc=ctx'ize φs; φσ = uσ φsc

-- FIXME: eat into stack var when present
rwAr :: Ar -> TSeq a -> TM a (TSeq a)
rwAr ar = under (fmap reverse . g . reverse)
    where g (tt@(TT x n):ts) = do {k <- lT ar n; if length ts>=k then let (a,r)=splitAt k ts in (Σ x (Nm.singleton n (reverse a)):)<$>g r else (tt:) <$> g ts}
          g (t:ts)           = (t:)<$>g ts
          g []               = pure []

          under f (t@SV{}:ts) = (t:)<$>f ts
          under f ts          = f ts

mc u c s = ms u c s `onM` (rwAr (ars c)<=<peek s)

hasC = any (\t -> case unA t of Just (TC{},_) -> True;_ -> False)

ce c = traverse (βc c)

ms :: (Nt a -> T a -> T a -> TM a (Subst a))
   -> Nt a -> Subst a -> TSeq a -> TSeq a -> TM a (Subst a)
ms u c s t0e@(SV _ nm₀:t0) t1e@(SV _ nm₁:t1)
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in mc u c (iSV nm₀ []$iSV nm₁ uws s) t0 res
    | hasC t0 = do {t0' <- ce (tβ c) t1; ms u c s t0' t1e}
    -- FIXME: eat based on constructor arity
    | otherwise = throwError$LE t0e t1e
  where n0=length t0;n1=length t1
ms u c s t0e@(SV _ n:t0) t1
    | n0<=n1 = let (uws, res) = splitFromLeft n0 t1
               in mc u c (iSV n uws s) t0 res
    | hasC t1 = do {t1' <- ce (tβ c) t1; ms u c s t0e t1'}
    -- FIXME: make sure this doesn't loop indefinitely?
    | otherwise = throwError$LE t0e t1
  where n0=length t0;n1=length t1
ms u c s t0 t1e@(SV _ n:t1)
    | n0>=n1 = let (uws, res) = splitFromLeft n1 t0
               in mc u c (iSV n uws s) res t1
    | hasC t0 = do {t0' <- ce (tβ c) t1; ms u c s t0' t1e}
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

-- ≺
lt :: Nt a -> T a -> T a -> TM a (Subst a)
lt c t0@(Σ _ σ0) t1@(Σ _ σ1) | σ0 `Nm.isSubmapOf` σ1 = mσ lt c σ0 σ1
                             | otherwise = sf t0 t1
lt _ t0@(TT _ tt0) t1@(TT _ tt1) | tt0==tt1 = pure mempty
                                 | otherwise = sf t0 t1
lt _ (TV _ n0) (TV _ n1) | n0==n1 = pure mempty
lt _ t0 t1@(TV _ n) = c1 n t0 t1
lt _ t0@(TV _ n) t1 = c1 n t1 t0
lt c (QT _ ts0) (QT _ ts1) = mTS c ts0 ts1
lt c t0 t1 | Just (TC _ n0, a0) <- unA t0, Just (TC _ n1, a1) <- unA t1, n0==n1 = ms lt c mempty a0 a1
lt c t0 t1 | Just{} <- unA t0 = do {t0' <- βc (tβ c) t0; lt c t0' t1}
lt c t0 t1 | Just{} <- unA t1 = do {t1' <- βc (tβ c) t1; lt c t0 t1'}
lt c t0@(Ρ _ n σ0) t1@(Σ _ σ1)
    | occρ n σ1 = throwError$O t0 t1
    | σ0 `Nm.isSubmapOf` σ1 = iTV n t1 <$> mσ lt c σ0 σ1
    | otherwise = sf t0 t1
    -- TODO: Σ, TT
lt _ t0@(TT _ n) t1@(Σ _ a) | Just [] <- Nm.lookup n a = pure mempty
                            | otherwise = sf t0 t1
lt c t0@(Σ _ σ0) t1@(Ρ _ n σ1) | occρ n σ0 = throwError$O t1 t0
                               | otherwise = do {(_,g) <- nρ n (σ0<>σ1); g<$>mσ lt c σ0 σ1}
lt _ t@QT{} (Ρ _ n σ) | Nm.null σ = pure (sTV n t)
-- lt _ (Ρ _ n σ) t@QT{} | Nm.null σ = pure (sTV n t)
lt c t0@(Ρ _ n0 σ0) t1@(Ρ _ n1 σ1) | occρ n0 σ1 = throwError$O t0 t1
                                   | occρ n1 σ0 = throwError$O t1 t0
                                   -- TODO: should we allow ρ to expand? we handle it exactly different on line 426
                                   | σ0 `Nm.isSubmapOf` σ1 = mσ lt c σ0 σ1
                                   | otherwise = sf t0 t1
lt _ t0@(TP _ l0) t1@(TP _ l1) | l0==l1 = pure mempty
                               | otherwise = sf t0 t1
lt _ t0@TP{} t1@QT{} = sf t0 t1; lt _ t0@QT{} t1@TP{} = sf t0 t1
lt _ t0@TP{} t1@TT{} = sf t0 t1; lt _ t0@TT{} t1@TP{} = sf t0 t1
lt _ t0@TT{} t1@QT{} = sf t0 t1; lt _ t0@QT{} t1@TT{} = sf t0 t1
lt _ t0@TP{} t1@Σ{} = sf t0 t1; lt _ t0@Σ{} t1@TP{} = sf t0 t1
lt _ SV{} _ = ie; lt _ _ SV{} = ie

βc c t = do {cs <- gets (tds.lo); lΒ (c<>cs) t}

mTS :: Nt a -> TS a -> TS a -> TM a (Subst a)
mTS c = mtsc c mempty
-- FIXME: if we generalize on the right we should check it still matches on the left?

mtsc :: Nt a -> Subst a -> TS a -> TS a -> TM a (Subst a)
mtsc c s (TS l0 r0) (TS l1 r1) = do {s' <- mc (\cϵ t0 t1 -> lt cϵ t1 t0) c s l0 l1; mc lt c s' r0 r1}

liftClone :: TS a -> TM a (TS a)
liftClone ts = do {u <- gets maxT; let (w, ts') = cloneSig u ts in modify (\s -> s {maxT = w}) $> ts'}

lT :: Ar -> Nm a -> TM a Int
lT ex n@(Nm _ (U u) _) = do
    ar <- gets (arit.lo)
    case IM.lookup u ar of
        Just i  -> pure i
        Nothing -> case IM.lookup u ex of
            Just i  -> pure i
            Nothing -> throwError$AM n

lA :: IM.IntMap (TS a) -> Nm a -> TM a (TS a)
lA es n@(Nm _ (U i) _) = do
    b <- gets (fns.lo)
    case IM.lookup i b of
        Just ts -> liftClone ts
        Nothing -> case IM.lookup i es of
            Just ts -> liftClone ts
            Nothing -> throwError$IS n

tM :: Ext a -> M a a -> StateT Int (Either (TE a)) (M a (TS a), Ext a)
tM c m = StateT $ \i -> (\(x,y,z) -> ((x,y),z)) <$> runTM i (tMM c m)

tMM :: Ext a -> M a a -> TM a (M a (TS a))
tMM b (M is ds) = M is <$> tD b ds

tD :: Ext a -> [D a a] -> TM a [D a (TS a)]
tD b ds = traverse_ tD0 ds *> traverse (tD1 b) ds

-- `e `a mult
-- `a mult
--
-- evaluator pinches stack vars off pattern match...
tAS :: Int -> Ext a -> [A (TS a)] -> ASeq a -> Either (TE a) ((TS a, ASeq (TS a)), Int)
tAS u b s a = fmap π₁₃ $ runTM u $ do
    (t0,s0) <- sseq n (aLs a) mempty (reverse s)
    (t1,s1) <- tseq b s0 a
    (t2,s2) <- cat n s1 t0 (aLs t1)
    (,) <$> s2@*t2 <*> taseq (s2@*) t1
  where π₁₃ (x,_,z)=(x,z); n=π b

{-# SCC tD0 #-}
tD0 :: D a a -> TM a ()
tD0 (F _ n ts _)  = iFn n ts
tD0 (TD _ n vs t) = iTD n vs t *> cA t

{-# SCC tD1 #-}
tD1 :: Ext a -> D a a -> TM a (D a (TS a))
tD1 _ (TD x n vs t)         = pure (TD x n vs t)
tD1 b (F _ n ts as) = do
    (as', s) <- tseq b mempty as
    s' <- mtsc (π b) s (aLs as') ts
    as''<- taseq (s'@*) as'
    pure (F ts (n$>ts) ts as'')

sseq :: Nt a -> a -> Subst a -> [A (TS a)] -> TM a (TS a, Subst a)
sseq _ l s []     = do {a <- fsv l "A"; pure (TS [a] [a], s)}
sseq b l s (a:as) = do
    (tϵ, s0) <- sseq b l s as
    cat b s0 (aL a) tϵ

tseq :: Ext a -> Subst a -> ASeq a -> TM a (ASeq (TS a), Subst a)
tseq _ s (SL l [])     = do {a <- fsv l "A"; pure (SL (TS [a] [a]) [], s)}
tseq b s (SL l (a:as)) = do
    (a',s0) <- tae b s a
    (SL tϵ as', s1) <- tseq b s0 (SL l as)
    (t, s2) <- cat (π b) s1 (aL a') tϵ
    -- tϵ' <- s2@*tϵ; t' <- s2@*t
    -- pure $ traceShow (traceCat a' as' (aL a') tϵ' t') (SL t (a':as'), s2)
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
cat :: Nt a -> Subst a -> TS a -> TS a -> TM a (TS a, Subst a)
cat c s (TS l0 r0) (TS l1 r1) = do
    (_, s') <- susc c s r0 l1
    pure (TS l0 r1, s')

  -- check that user-supplied signatures have at most one stack variable, and that it occurs at the leftmost

fr :: a -> T.Text -> TM a (Nm a)
fr l t = state (\(TSt m s) -> let n=m+1 in (Nm t (U n) l, TSt n s))

ftv, fsv, erv :: a -> T.Text -> TM a (T a)
ftv l n = TV l <$> fr l n; fsv l n = SV l <$> fr l ("'" <> n)
erv l n = Ρ l <$> fr l n <*> pure Nm.empty

exps :: a -> TS a -> TM a (TS a)
exps _ t@(TS (SV{}:_) _) = pure t; exps _ t@(TS _ (SV{}:_)) = pure t
exps x (TS l r) = do {ᴀ <- fsv x "A"; pure (TS (ᴀ:l) (ᴀ:r))}

tae :: Ext a -> Subst a -> A a -> TM a (A (TS a), Subst a)
tae _ s (B l Dip)  = do {a <- fsv l "A"; b <- ftv l "b"; c <- fsv l "C"; pure (B (TS [a, b, QT l (TS [a] [c])] [c,b]) Dip, s)}
tae _ s (B l Doll) = do {a <- fsv l "A"; b <- fsv l "B"; pure (B (TS [a, QT l (TS [a] [b])] [b]) Doll, s)}
tae b s a = do
    (a',s') <- ta b s a
    let t=aL a'
    t' <- exps (aL a) t
    pure (a' {aL = t'}, s')

ib l = B (TS [TP l Int, TP l Int] [TP l Int])
rel l = B (TS [TP l Int, TP l Int] [ʙ l])

ta :: Ext a -> Subst a -> A a -> TM a (A (TS a), Subst a)
ta _ s (L l lit@I{})   = pure (L (TS [] [TP l Int]) lit, s)
ta _ s (L l lit@Str{}) = pure (L (TS [] [TP l String]) lit, s)
ta b s (V _ n)         = do {ts <- lA (fns b) n; pure (V ts (n$>ts), s)}
ta _ s (B l Un)        = do {n <- ftv l "a"; pure (B (TS [n] []) Un, s)}
ta _ s (B l Dup)       = do {n <- ftv l "a"; pure (B (TS [n] [n,n]) Dup, s)}
ta _ s (B l Swap)      = do {a <- ftv l "a"; b <- ftv l "b"; pure (B (TS [a,b] [b,a]) Swap, s)}
ta _ s (B l Plus)      = pure (ib l Plus, s)
ta _ s (B l Minus)     = pure (ib l Minus, s)
ta _ s (B l Mul)       = pure (ib l Mul, s)
ta _ s (B l Div)       = pure (ib l Div, s)
ta _ s (B l Eq)        = pure (rel l Eq, s)
ta _ s (B l Gt)        = pure (rel l Gt, s)
ta _ s (B l Lt)        = pure (rel l Lt, s)
ta b s (Q l as)        = do {(as', s') <- tseq b s as; pure (Q (TS [] [QT l (aLs as')]) as', s')}
ta b s (Inv _ a)       = do {(a', s') <- ta b s a; let TS l r = aL a' in pure (Inv (TS r l) a', s')}
ta b s (C l tt)        = do
    p <- lT (arit b) tt
    -- TODO: pad beginning not-inverse constructors with a₀ etc. not ρ₀?
    ρ <- pad l p
    let ts=TS ρ (ρ++[TT l tt]) in pure (C ts (tt$>ts), s)
ta b s (Pat _ as)      = do
    (as', s0) <- tS b s (aas as)
    sigs <- traverse (peekS s0.aLs) as'
    -- TODO: maybe "pick off" negatives here
    (t, s1) <- dU (π b) s0 sigs
    pure (Pat t (SL t as'), s1)

-- e.g. `e⁻¹ `e⁻¹ `e & `e⁻¹ `a⁻¹ `a & ... rewritten to K⁻¹ K⁻¹ somehow
-- basically if `e⁻¹ { ... } and `a⁻¹ { ... } have a type that UNIFIES then we can "pick-2"
-- FIXME pop off all inverse constructors e.g. `t⁻¹ `f⁻¹
ai :: [T a] -> TM a [(Nm a, [T a])]
ai ts | Just (tsϵ, TT _ n) <- unsnoc ts = pure [(n, tsϵ)]
      | Just (tsϵ, Σ l as) <- unsnoc ts = pure $ second (++tsϵ) <$> Nm.toList l as
      | otherwise = throwError (PM ts)

an :: Ar -> [(Nm a, [T a])] -> TM a (T a, [[T a]])
an ar as = do
    (tas, tss) <- unzip<$>traverse (\(nm,ts) -> do{n<-lT ar nm; when (n>length ts) (error"Internal error?") $> (ts /| n)}) as
    pure (Σ l (Nm.fromList (zip nms tss)), tas)
  where l=loc (fst$head as); nms=map fst as

pad :: a -> Int -> TM a (TSeq a)
pad l n = traverse (\i -> erv l ("ρ"<>pᵤ i)) [1..n]

{-# SCC dU #-}
dU :: Nt a -> Subst a -> [TS a] -> TM a (TS a, Subst a)
dU c s tss = do
    ρ <- zipWithM pad (tLs<$>ls) [ rm-length r | r <- rs ]
    let ls'=zipWith tuck ρ ls; rs'=zipWith tuck ρ rs
    al <- traverse ai ls'
    (σ,ul) <- an (ars c) (concat al)
    (l',s') <- urs s ul; (r',s'') <- frs s' rs'
    -- pure $ let t=TS (l'++[σ]) (r') in traceShow (traceΦ tss t) (t, s'')
    pure (TS (l'++[σ]) r', s'')
  where ls=map tlefts tss; rs=map trights tss
        rm=maximum (length<$>map trights tss)

        tuck ts0 (t@SV{}:ts1) = t:ts0++ts1

        frs sϵ [t]    = pure (t, sϵ)
        frs sϵ (t:ts) = do {(tr,s0) <- frs sϵ ts; φsc c s0 tr t}

        urs sϵ [t]    = pure (t, sϵ)
        urs sϵ (t:ts) = do {(tr,s0) <- urs sϵ ts; usc c s0 tr t}

        traceΦ ts σ = vsep (pa<$>ts) <#> "-" <#> pretty σ <> hardline
        pa (TS l r) | Just (a, t@TT{}) <- unsnoc l = pretty t <+> ":" <+> pretty (TS a r)

tS :: Ext a -> Subst a -> [ASeq a] -> TM a ([ASeq (TS a)], Subst a)
tS _ s []     = pure ([], s)
tS b s (a:as) = do {(a',s') <- tseq b s a; first (a':) <$> tS b s' as}

onM :: Monad m => (b -> b -> m c) -> (a -> m b) -> a -> a -> m c
onM g f x y = do {x' <- f x; y' <- f y; g x' y'}

(@<>) :: (Monoid m, Foldable f) => (a -> m) -> f a -> m
(@<>) = foldMap

ie=error"internal error."

eqKeys :: Nm.NmMap a -> Nm.NmMap b -> Bool
eqKeys (Nm.NmMap x0 _) (Nm.NmMap x1 _) = IM.keys x0==IM.keys x1
