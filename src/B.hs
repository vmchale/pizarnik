module B ( BE, β ) where

import           A
import           D
import           Data.Functor  (($>))
import qualified Data.IntMap   as IM
import           Nm
import           Prettyprinter (Pretty (pretty), (<+>))

type Β a=IM.IntMap (T a)

newtype BE a = TCA (Nm a) deriving Functor

instance Pretty a => Pretty (BE a) where pretty (TCA n) = pretty (loc n) <> ":" <+> "Type constructor not fully applied"

β :: Cs a -> Nm a -> [T a] -> Either (BE a) (T a)
β c n bs = let (vs,t) = lC n c in ($>loc n) <$> bS (IM.fromList$zipWith (\(Nm _ (U u) _) b -> (u,b)) vs bs) t

lC :: Nm a -> Cs a -> ([Nm a], T a)
lC n@(Nm _ (U i) _) = IM.findWithDefault (error("Internal error. Type synonym '" ++ show n ++ "' not in scope")) i

bS :: Β a -> T a -> Either (BE a) (T a)
bS st (TV _ n@(Nm _ (U j) _)) | Just t <- IM.lookup j st = Right t | otherwise = Left $ TCA n
-- avoid TCA errors not by user when substituting
bS st t@(TA x t0 t1) | Just (th,ts) <- unA t = foldl (TA x) th <$> traverse (bS st) ts -- avoid expanding infinite (e.g. List(a))
                     | otherwise = TA x <$> bS st t0 <*> bS st t1
bS _ t@TT{} = pure t; bS _ t@TP{} = pure t
bS st (Σ x tss) = Σ x <$> traverse (traverse (bS st)) tss
bS st (QT x sig) = QT x <$> tTS (bS st) sig
bS st (UU x ts) = UU x <$> traverse (bS st) ts
bS _ t@TC{} = pure t
