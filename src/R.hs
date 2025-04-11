{-# LANGUAGE RankNTypes #-}

module R ( Ex (..)
         , Bd, Bt
         , Rs (..)
         , RE (MDF, MDC, MDT)
         , rM
         ) where

import           A
import           Control.Arrow                    ((&&&))
import           Control.Exception                (Exception (..))
import           Control.Monad                    ((<=<))
import           Control.Monad.Except             (throwError)
import           Control.Monad.Trans.State.Strict (StateT, get, gets, modify, put, runStateT)
import           Data.Bifunctor                   (first, second)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import           Data.Typeable                    (Typeable)
import           Lens.Micro                       (Lens', set)
import           Lens.Micro.Extras                (view)
import           Nm
import           Nm.Map                           (NmMap (NmMap))
import           Pr
import           Prettyprinter                    (Pretty (..), (<+>))

infixr 5 @~

data RE a = IllScoped (Nm a) | D (Nm a) | MDF !MN | MDC !MN | MDT !MN

instance Pretty a => Pretty (RE a) where
    pretty (IllScoped n) = pretty (loc n) <> ":" <+> "Not in scope:" <+> sq n
    pretty (D n)         = pretty (loc n) <> ":" <+> sq n <+> "has already been defined"
    pretty (MDF m)       = "Module" <+> sq m <+> "imports the same function from different sources."
    pretty (MDC m)       = "Module" <+> sq m <+> "imports the same type from different sources."
    pretty (MDT m)       = "Module" <+> sq m <+> "imports the same constructor from different sources."

instance Pretty a => Show (RE a) where show=show.pretty
instance (Pretty a, Typeable a) => Exception (RE a)

type Bd=IM.IntMap Int; type Bt=IM.IntMap Int

data Ex = Ex { bf, bt, btt :: Bd }
data Rs = Rs { max_ :: !Int, ex :: !Ex, btv, bsv :: Bt }

instance Pretty Ex where pretty (Ex v t a) = pBound v <##> pBound t <##> pBound a

instance Show Ex where show=show.pretty

bfl,btl,bal :: Lens' Ex Bd
btl f (Ex ff t a) = (\x -> Ex ff x a) <$> f t
bfl f (Ex ff t a) = (\x -> Ex x t a) <$> f ff
bal f (Ex ff t a) = Ex ff t <$> f a

bvl,bsl :: Lens' Rs Bt
bsl f (Rs m e t v) = Rs m e t <$> f v
bvl f (Rs m e t v) = (\x -> Rs m e x v) <$> f t

type RM x = StateT Rs (Either (RE x))

runRM :: Int -> RM a (f a) -> Either (RE a) (Int, Ex, f a)
-- TODO: true, false special cases?
runRM u = fmap (\(x,Rs u' b _ _) -> (u',b,x)).flip runStateT (Rs u (Ex IM.empty IM.empty IM.empty) IM.empty IM.empty)

rTs :: Ex -> TSeq a -> RM a (TSeq a)
rTs b = traverse (b@~)

rSig :: Ex -> TS a -> RM a (TS a)
rSig b (TS l r) = TS <$> rTs b l <*> rTs b r

(@~) :: Ex -> T a -> RM a (T a)
(@~) _ t@TP{}      = pure t
(@~) b (TT x n)    = TT x <$> lA b n
(@~) b (TC x n)    = TC x <$> lT b n
(@~) _ (TV x n)    = TV x <$> fr n
(@~) _ (SV x n)    = SV x <$> frs n
(@~) b (TA x t t') = TA x <$> b@~t <*> b@~t'
(@~) b (QT x tS)   = QT x <$> rSig b tS
(@~) b (Σ x ts)    = Σ x <$> traverse (rTs b) (rkeys (btt b) ts)
(@~) b (UU x ts)   = UU x <$> rTs b ts

doLocal :: RM a b -> RM a b
doLocal act = do
    (tvs,svs) <- gets (btv &&& bsv)
    act <* modify (\r -> r { btv = tvs, bsv = svs })

frv :: Lens' Rs Bt -> Nm a -> RM x (Nm a)
frv l (Nm t (U i) x) = do
    st <- get
    let bϵ=view l st
    case IM.lookup i bϵ of
        Nothing -> let j=max_ st+1 in put (set l (IM.insert i j bϵ) (st {max_ = j})) $> Nm t (U j) x
        Just j  -> pure $ Nm t (U j) x

fr, frs :: Nm a -> RM x (Nm a)
fr=frv bvl; frs=frv bsl

fra :: Ex -> [Int] -> RM a [(Int,Int)]
fra b i = do
    s <- get
    let ex'=ex s; t=btt ex'; (i',i_) = g (t<>btt b) i
        u=max_ s; u'=u+length i'; m=zip i' [u..u']
    put (s { max_ = u', ex = set bal (IM.fromList m<>t) ex' }) $> m<>i_
  where g _ []     = ([], [])
        g e (n:ii) = (case IM.lookup n e of {Just iϵ -> second ((n,iϵ):); Nothing -> first (n:)}) (g e ii)

frd :: Lens' Ex Bd -> Ex -> Nm a -> RM a (Nm a)
frd l b n@(Nm t (U i) x) | i `IM.member` view l b = throwError (D n)
                         | otherwise = do {st <- get; let exϵ=ex st; bl=view l exϵ in if i `IM.member` bl then throwError (D n) else let j=max_ st+1 in put (st { max_ = j, ex=set l (IM.insert i j bl) exϵ }) $> Nm t (U j) x}

frt, frn, frtt :: Ex -> Nm a -> RM a (Nm a)
frt=frd btl; frn=frd bfl; frtt=frd bal

rAs :: Ex -> ASeq a -> RM a (ASeq a)
rAs b (SL x as) = SL x <$> traverse (rA b) as

lD :: (Ex -> Bd) -> Ex -> Nm a -> RM a (Nm a)
lD g b n@(Nm t (U j) x) = do
    l <- gets (g.ex)
    case IM.lookup j l of
        Just k -> pure $ Nm t (U k) x
        Nothing -> case IM.lookup j (g b) of
            Just k  -> pure $ Nm t (U k) x
            Nothing -> throwError (IllScoped n)

lT, lV,lA :: Ex -> Nm a -> RM a (Nm a)
lT=lD bt; lV=lD bf
lA _ n@(Nm _ (U (-1)) _) = pure n
lA _ n@(Nm _ (U (-2)) _) = pure n
lA b n                   = lD btt b n

rA :: Ex -> A a -> RM a (A a)
rA b (V x n)           = V x <$> lV b n
rA _ a@B{}             = pure a
rA b (C x tt)          = C x <$> lA b tt
rA _ a@L{}             = pure a
rA b (Q x as)          = Q x <$> rAs b as
rA b (Inv x a)         = Inv x <$> rA b a
rA b (Pat x (SL l αs)) = Pat x <$> (SL l <$> traverse (rAs b) αs)

rM :: Int -> Ex -> M a a -> Either (RE a) (Int, Ex, M a a)
rM u b (M is ds) = runRM u (M is <$> ((\d -> do {t <- gets (btt.ex); traverse (rD1 (ttl b t)) d}) <=< traverse (rD0 b)) ds)
    where ttl (Ex f c t) t' = Ex f c (t<>t')

rkeys :: Bd -> NmMap (TSeq a) -> NmMap (TSeq a)
rkeys b = nmMapKeys (\i -> IM.findWithDefault i i b)

fkeys :: Ex -> NmMap (TSeq a) -> RM a (NmMap (TSeq a))
fkeys b m@(NmMap x _) = do
    e <- fra b (IM.keys x)
    pure $ rkeys (IM.fromList e) m

nmMapKeys f (NmMap x a) = NmMap (IM.mapKeys f x) (IM.mapKeys f a)

t0s b = traverse (t0 b)

t0 :: Ex -> T a -> RM a (T a)
t0 b (TT x n) = TV x<$>frtt b n; t0 b (Σ x ts) = Σ x <$> fkeys b ts
t0 b (QT x (TS l r)) = QT x <$> (TS <$> t0s b l <*> t0s b r)
t0 b (TA x t t') = TA x <$> t0 b t <*> t0 b t'; t0 b (UU x ts) = UU x <$> t0s b ts
t0 _ t@TC{} = pure t; t0 _ t@TV{} = pure t; t0 _ t@TP{} = pure t

rD0 :: Ex -> D a a -> RM a (D a a)
rD0 b (F l n t as)  = F l <$> frn b n <*> pure t <*> pure as
rD0 b (TD l n vs t) = TD l <$> frt b n <*> pure vs <*> t0 b t

rD1 :: Ex -> D a a -> RM a (D a a)
rD1 b (F l n t as)  = F l n <$> doLocal (rSig b t) <*> rAs b as
rD1 b (TD l n vs t) = do {(vs',t') <- doLocal ((,) <$> traverse fr vs <*> (b@~t)); pure (TD l n vs' t')}
