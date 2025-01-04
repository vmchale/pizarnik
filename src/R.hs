{-# LANGUAGE RankNTypes        #-}

module R ( Ex (..)
         , Bd, Bt
         , Rs (..)
         , RE (MDF, MDC)
         , rM
         ) where

import           A
import           Control.Arrow                    ((&&&))
import           Control.Exception                (Exception (..))
import           Control.Monad                    ((<=<))
import           Control.Monad.Except             (throwError)
import           Control.Monad.Trans.State.Strict (StateT, get, gets, modify, put, runStateT)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import           Data.Typeable                    (Typeable)
import           Lens.Micro                       (Lens', set)
import           Lens.Micro.Extras                (view)
import           Nm
import           Pr
import           Prettyprinter                    (Pretty (..), (<+>))

infixr 5 @~

data RE a = IllScoped (Nm a) | D (Nm a) | MDF !MN | MDC !MN

instance Pretty a => Pretty (RE a) where
    pretty (IllScoped n) = pretty (loc n) <> ":" <+> "Not in scope:" <+> sq (pretty n)
    pretty (D n)         = pretty (loc n) <> ":" <+> sq (pretty n) <+> "has already been defined"
    pretty (MDF m)       = "Module" <+> sq (pretty m) <+> "imports the same function from different sources."
    pretty (MDC m)       = "Module" <+> sq (pretty m) <+> "imports the same type from different sources."

instance Pretty a => Show (RE a) where show=show.pretty
instance (Pretty a, Typeable a) => Exception (RE a)

type Bd=IM.IntMap Int; type Bt=IM.IntMap Int

data Ex = Ex { bf, bt :: Bd }
data Rs = Rs { max_ :: !Int, ex :: !Ex, btv :: Bt, bsv :: Bt }

instance Pretty Ex where pretty (Ex v t) = pBound v <##> pBound t

instance Show Ex where show=show.pretty

stv tv r = r { btv = tv }; ssv sv r = r { bsv = sv }

bfl,btl :: Lens' Ex Bd
btl f (Ex ff t) = Ex ff <$> f t
bfl f (Ex ff t) = (\x -> Ex x t) <$> f ff

bvl,bsl :: Lens' Rs Bt
bsl f (Rs m e t v) = Rs m e t <$> f v
bvl f (Rs m e t v) = (\x -> Rs m e x v) <$> f t

type RM x = StateT Rs (Either (RE x))

runRM :: Int -> RM a (f a) -> Either (RE a) (Int, Ex, f a)
runRM u = fmap (\(x,Rs u' b _ _) -> (u',b,x)).flip runStateT (Rs u (Ex IM.empty IM.empty) IM.empty IM.empty)

rTs :: Ex -> TSeq a -> RM a (TSeq a)
rTs b = traverse (b@~)

rSig :: Ex -> TS a -> RM a (TS a)
rSig b (TS l r) = TS <$> rTs b l <*> rTs b r

(@~) :: Ex -> T a -> RM a (T a)
(@~) _ t@TP{}      = pure t
(@~) _ t@TT{}      = pure t
(@~) b (TC x n)    = TC x <$> lT b n
(@~) _ (TV x n)    = TV x <$> fr n
(@~) _ (SV x n)    = SV x <$> frs n
(@~) b (TA x t t') = TA x <$> b @~ t <*> b @~ t'
(@~) b (QT x tS)   = QT x <$> rSig b tS
(@~) b (Σ x ts)    = Σ x <$> traverse (rTs b) ts
(@~) b (TI x t)    = TI x <$> b@~t

doLocal :: RM a b -> RM a b
doLocal act = do
    (tvs,svs) <- gets (btv &&& bsv)
    act <* modify (stv tvs.ssv svs)

ct :: Ex -> TS a -> RM a (TS a)
ct b (TS l r) = doLocal $ TS <$> rTs b l <*> rTs b r

frv :: Lens' Rs Bt -> Nm a -> RM x (Nm a)
frv l (Nm t (U i) x) = do
    st <- get
    let bϵ=view l st
    case IM.lookup i bϵ of
        Nothing -> let j=max_ st+1 in put (set l (IM.insert i j bϵ) (st {max_ = j})) $> Nm t (U j) x
        Just j  -> pure $ Nm t (U j) x

fr, frs :: Nm a -> RM x (Nm a)
fr=frv bvl; frs=frv bsl

frd :: Lens' Ex Bd -> Ex -> Nm a -> RM a (Nm a)
frd l b n@(Nm t (U i) x) | i `IM.member` view l b = throwError (D n)
                         | otherwise = do {st <- get; let exϵ=ex st; bl=view l exϵ in if i `IM.member` bl then throwError (D n) else let j=max_ st+1 in put (st { max_ = j, ex=set l (IM.insert i j bl) exϵ }) $> Nm t (U j) x}

frt, frn :: Ex -> Nm a -> RM a (Nm a)
frt=frd btl; frn=frd bfl

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

lT, lV :: Ex -> Nm a -> RM a (Nm a)
lT=lD bt; lV=lD bf

rA :: Ex -> A a -> RM a (A a)
rA b (V x n)           = V x <$> lV b n
rA _ a@B{}             = pure a
rA _ a@C{}             = pure a
rA _ a@L{}             = pure a
rA b (Q x as)          = Q x <$> rAs b as
rA b (Inv x a)         = Inv x <$> rA b a
rA b (Pat x (SL l αs)) = Pat x <$> (SL l <$> traverse (rAs b) αs)

rM :: Int -> Ex -> M a a -> Either (RE a) (Int, Ex, M a a)
rM u b (M is ds) = runRM u (M is <$> (traverse (rD1 b) <=< traverse (rD0 b)) ds)

rD0 :: Ex -> D a a -> RM a (D a a)
rD0 b (F l n t as)  = F l <$> frn b n <*> pure t <*> pure as
rD0 b (TD l n vs t) = TD l <$> frt b n <*> pure vs <*> pure t

rD1 :: Ex -> D a a -> RM a (D a a)
rD1 b (F l n t as)  = F l n <$> ct b t <*> rAs b as
rD1 b (TD l n vs t) = do {(vs',t') <- doLocal $ (,) <$> traverse fr vs <*> (b @~ t); pure (TD l n vs' t')}
