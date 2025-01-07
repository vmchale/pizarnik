module B ( Cs, BE, β ) where

import           A
import qualified Data.IntMap   as IM
import           Nm
import           Prettyprinter (Pretty (pretty), (<+>))

type Cs a=IM.IntMap ([Nm a], T a); type Β a=IM.IntMap (T a)

newtype BE a = TCA (Nm a)

instance Pretty a => Pretty (BE a) where pretty (TCA n) = pretty (loc n) <> ":" <+> "Type constructor not fully applied"

β :: Cs a -> Nm a -> [T a] -> Either (BE a) (T a)
β c n bs = let (vs,t) = lC n c in bS (IM.fromList$zipWith (\(Nm _ (U u) _) b -> (u,b)) vs bs) t

lC :: Nm a -> Cs a -> ([Nm a], T a)
lC (Nm _ (U i) _) = IM.findWithDefault (error "Internal error. Constructor not in scope?") i

bS :: Β a -> T a -> Either (BE a) (T a)
bS st (TV _ n@(Nm _ (U j) _)) =
    case IM.lookup j st of
        Nothing -> Left $ TCA n
        Just t  -> Right t
-- avoid TCA errors not by user when substituting
bS st t@(TA x t0 t1) | not (eA t) = TA x <$> bS st t0 <*> bS st t1
                     | otherwise = pure t
bS st (TI x t) = TI x <$> bS st t
bS _ t@TT{} = pure t; bS _ t@TP{} = pure t
bS st (Σ x tss) = Σ x <$> traverse (traverse (bS st)) tss
bS st (QT x sig) = QT x <$> tTS (bS st) sig
